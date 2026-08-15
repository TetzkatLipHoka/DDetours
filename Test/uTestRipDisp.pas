unit uTestRipDisp;

(*
 * Regression tests for CorrectRipDisp / the instruction decoder.
 *
 * When a prologue is copied into the trampoline, rip-relative instructions have
 * to be rewritten. Several defects lived in that path, and they only show up
 * inside the hooked process as an access violation at a random address - hence
 * these tests:
 *
 *   1) The corrected displacement was written into the LAST 4 bytes of the
 *      instruction. If an immediate follows, disp32 sits BEFORE it, so both the
 *      displacement and the immediate were destroyed.
 *      (Delphi's x64 unit initialization: SUB dword ptr [rip+d], 1)
 *   2) In the absolute branch (trampoline more than 2 GB away) the immediate
 *      was not copied at all, so the CPU consumed the following POP byte as the
 *      immediate.
 *   3) That branch used (R|E)AX as scratch register - fatal for instructions
 *      that use AX/DX implicitly (MUL, DIV, IDIV, CMPXCHG).
 *   4) GetInstOpCodes counted the opcode twice for FPU instructions.
 *   5) CRC32 ($0F$38 with a mandatory prefix) was rejected by the decoder, so
 *      ModRm and displacement were never consumed and InstSize came out at 4
 *      instead of 9.
 *   6) Prf_Vex2/Prf_Vex3 share the Prf_VEX bit, so "and <> 0" matched the other
 *      VEX form too and both VEX lengths were one byte too long.
 *
 * IMPORTANT (1): the functions under test are written in assembler so the
 * rip-relative instruction is among the FIRST ones. A regular Pascal function
 * starts with its stack frame, DDetours would only relocate those bytes, and
 * the interesting instruction would never reach the relocation code - the test
 * would pass no matter what is broken.
 *
 * IMPORTANT (2): every function is padded with NOPs. An x64 hook patch is up to
 * 14 bytes; a shorter function gets overwritten past its end, taking the next
 * function with it, and the test then fails for a reason that has nothing to do
 * with what it is meant to check.
 *
 * The rarely taken absolute branch is forced by building with
 *   -DDDETOURS_FORCE_ABSRIP
 * Both runs (with and without the define) must be green.
 *)

interface

uses
  DUnitX.TestFramework;

type
  [TestFixture]
  TRipDispTests = class(TObject)
  public
    // displacement vs. immediate
    [Test] procedure Disp_FollowedBy_Imm8;
    [Test] procedure Disp_FollowedBy_Imm32;
    // implicit register use
    [Test] procedure ImplicitEax_Mul;
    [Test] procedure ImplicitEax_CmpXchg;
    // opcode maps
    [Test] procedure OpcodeMap_Fpu;
    [Test] procedure OpcodeMap_TwoByte;
    [Test] procedure OpcodeMap_ThreeByte_MandatoryPrefix;
    [Test] procedure OpcodeMap_Vex2;
    [Test] procedure OpcodeMap_Vex3;
  end;

  {
    A function that branches back into the bytes an inline patch would occupy
    cannot be hooked at all - relocation does not help, because the jump goes
    to an address that no longer holds the original code. DDetours has to
    refuse such a target instead of corrupting it.

    Found in the wild in Vcl.Imaging.pngimage.TPngImage.InitializeGamma:

        xor  edx, edx              ; +0
        mov  ecx, edx              ; +2   <- loop target
        ...
        jne  -22                   ; back to +2
        ret

    A 5 byte patch at +0 swallows the target; the first iteration runs the
    JMP, the second one executes its displacement as code. The process then
    dies somewhere unrelated - here it read the NOP padding as a pointer.
  }
  [TestFixture]
  TPatchAreaTests = class(TObject)
  public
    // loop target inside the patch -> must be refused
    [Test] procedure LoopIntoPatchArea_IsRefused;
    // same shape but the loop starts past the patch -> must still hook
    [Test] procedure LoopBeyondPatchArea_IsHooked;
  end;

  {
    Import thunks: JMP dword/qword ptr [slot].

    Delphi emits one of these per imported API (System.GetCurrentThreadId,
    System.ExitProcess, ...) - 6 bytes of jump plus 2 bytes of padding. They
    are attractive hook targets because they are the funnel for every call to
    that API, and a profiler that instruments everything hits thousands of
    them.

    The whole thunk is a single instruction, so the patch swallows all of it
    and the trampoline has to carry a working copy: absolute on x86,
    rip-relative (and therefore relocated) on x64.
  }
  [TestFixture]
  TImportThunkTests = class(TObject)
  public
    [Test] procedure ImportThunk_IsRelocated;
  end;

  {
    Instruction length, checked straight at the decoder.

    Some encodings cannot be produced portably from Delphi's inline assembler,
    so they are fed to DecodeInst as raw bytes. A wrong length here is the
    worst kind of defect: everything after the instruction shifts, the
    trampoline is built from garbage, and the failure surfaces as an access
    violation at an unrelated address.
  }
  [TestFixture]
  TDecoderSizeTests = class(TObject)
  public
    [Test] procedure Moffs_OperandSizePrefix_DoesNotShrinkOffset;
  end;

implementation

uses
  System.SysUtils,
  DDetours,
  InstDecode;

// Globals, so the compiler addresses them rip-relative (x64) / absolute (x86).
var
  GCounter: Integer = 0;
  GFlag: Integer = 0;
  GFactor: UInt32 = 0;
  GExchange: Integer = 0;
  GFpuIn: Integer = 0;
  GFpuOut: Integer = 0;
  GByte: Byte = $AB;
  GCrcIn: UInt32 = $12345678;
  GVecA: array [0 .. 3] of UInt32 = ($11111111, $22222222, $33333333, $44444444);
  GVecB: array [0 .. 3] of UInt32 = (2, 3, 4, 5);

// SUB dword ptr [rip+d], 1  ->  83 2D <disp32> 01
function DecCounter: Integer;
asm
{$IFDEF CPUX64}
  sub   dword ptr [rip + GCounter], 1
  mov   eax, dword ptr [rip + GCounter]
{$ELSE}
  sub   dword ptr [GCounter], 1
  mov   eax, dword ptr [GCounter]
{$ENDIF}
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// MOV dword ptr [rip+d], imm32  ->  C7 05 <disp32> <imm32>
function SetFlagLarge: Integer;
asm
{$IFDEF CPUX64}
  mov   dword ptr [rip + GFlag], $12345678
  mov   eax, dword ptr [rip + GFlag]
{$ELSE}
  mov   dword ptr [GFlag], $12345678
  mov   eax, dword ptr [GFlag]
{$ENDIF}
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// MUL uses (R|E)AX and EDX implicitly
function MulByGlobal(x: UInt32): UInt32;
asm
{$IFDEF CPUX64}
  mov   eax, ecx
  mul   dword ptr [rip + GFactor]
{$ELSE}
  mul   dword ptr [GFactor]
{$ENDIF}
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// CMPXCHG uses (R|E)AX implicitly as the comparand
function CasGlobal(Expected, NewVal: Integer): Integer;
asm
{$IFDEF CPUX64}
  mov   eax, ecx
  lock cmpxchg dword ptr [rip + GExchange], edx
{$ELSE}
  lock cmpxchg dword ptr [GExchange], edx
{$ENDIF}
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// FPU: escape byte + ModRm
function FpuRoundTrip: Integer;
asm
{$IFDEF CPUX64}
  fild  dword ptr [rip + GFpuIn]
  fistp dword ptr [rip + GFpuOut]
  mov   eax, dword ptr [rip + GFpuOut]
{$ELSE}
  fild  dword ptr [GFpuIn]
  fistp dword ptr [GFpuOut]
  mov   eax, dword ptr [GFpuOut]
{$ENDIF}
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// two-byte opcode: 0F B6
function TwoByteLoad: UInt32;
asm
{$IFDEF CPUX64}
  movzx eax, byte ptr [rip + GByte]
{$ELSE}
  movzx eax, byte ptr [GByte]
{$ENDIF}
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// three-byte opcode WITH mandatory prefix: F2 0F 38 F1
function ThreeByteCrc: UInt32;
asm
  xor   eax, eax
{$IFDEF CPUX64}
  crc32 eax, dword ptr [rip + GCrcIn]
{$ELSE}
  crc32 eax, dword ptr [GCrcIn]
{$ENDIF}
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// two-byte VEX prefix: C5
function VexTwoByteLoad: UInt32;
asm
{$IFDEF CPUX64}
  vmovups xmm0, [rip + GVecA]
{$ELSE}
  vmovups xmm0, [GVecA]
{$ENDIF}
  vmovd   eax, xmm0
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// three-byte VEX prefix: C4 (VPMULLD lives in the 0F38 map, which the short
// $C5 form cannot encode)
function VexThreeByteMul: UInt32;
asm
{$IFDEF CPUX64}
  vmovups xmm1, [rip + GVecA]
  vpmulld xmm0, xmm1, [rip + GVecB]
{$ELSE}
  vmovups xmm1, [GVecA]
  vpmulld xmm0, xmm1, [GVecB]
{$ENDIF}
  vmovd   eax, xmm0
  db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// Loop target at +2, i.e. inside any inline patch (5 bytes on x86, up to 14 on
// x64). This must be refused.
function LoopIntoPatchArea: Integer;
asm
        xor     edx, edx           // +0, 2 bytes
@@loop:                            // +2  <- inside the patch
        inc     edx
        cmp     edx, 16
        jne     @@loop
{$IFDEF CPUX64}
        mov     eax, edx
{$ELSE}
        mov     eax, edx
{$ENDIF}
        db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// Same loop, but three 5-byte MOVs push its target to +15 - past the patch on
// both architectures. Guards the check against false positives.
function LoopBeyondPatchArea: Integer;
asm
        mov     eax, $11111111     // +0,  5 bytes
        mov     eax, $22222222     // +5,  5 bytes
        mov     eax, $33333333     // +10, 5 bytes
        xor     edx, edx           // +15
@@loop:                            // +17 <- beyond the patch
        inc     edx
        cmp     edx, 16
        jne     @@loop
        mov     eax, edx
        db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

// The imported routine an import thunk would forward to.
function ThunkTarget: Integer;
begin
  Result := 4711;
end;

var
  GImportSlot: Pointer = @ThunkTarget;    // stands in for an IAT entry

// JMP dword ptr [GImportSlot]  ->  FF 25 <abs32>   (x86)
// JMP qword ptr [rip+disp]     ->  FF 25 <rel32>   (x64, needs relocation)
function ImportThunk: Integer;
asm
{$IFDEF CPUX64}
        jmp     qword ptr [rip + GImportSlot]
{$ELSE}
        jmp     dword ptr [GImportSlot]
{$ENDIF}
        db $90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90,$90
end;

type
  TIntFunc  = function: Integer;
  TU32Func  = function: UInt32;
  TMulFunc  = function(x: UInt32): UInt32;
  TCasFunc  = function(Expected, NewVal: Integer): Integer;

// Detours that are never executed - the tests call the TRAMPOLINE, which holds
// the relocated copy of the original prologue. That copy is what is tested.
function DummyInt: Integer;                begin Result := 0; end;
function DummyU32: UInt32;                 begin Result := 0; end;
function DummyMul(x: UInt32): UInt32;      begin Result := 0; end;
function DummyCas(a, b: Integer): Integer; begin Result := 0; end;

{ TRipDispTests }

procedure TRipDispTests.Disp_FollowedBy_Imm8;
var
  tr: Pointer;
begin
  GCounter := 5;
  tr := InterceptCreate(@DecCounter, @DummyInt);
  Assert.IsTrue(tr <> nil, 'no trampoline');
  try
    TIntFunc(tr)();
    Assert.AreEqual(4, GCounter, 'immediate of SUB [rip+d],1 was destroyed');
    TIntFunc(tr)();
    Assert.AreEqual(3, GCounter, 'second call');
  finally
    InterceptRemove(tr);
  end;
end;

procedure TRipDispTests.Disp_FollowedBy_Imm32;
var
  tr: Pointer;
begin
  GFlag := 0;
  tr := InterceptCreate(@SetFlagLarge, @DummyInt);
  Assert.IsTrue(tr <> nil, 'no trampoline');
  try
    TIntFunc(tr)();
    Assert.AreEqual(Integer($12345678), GFlag,
      'immediate of MOV [rip+d],imm32 was destroyed');
  finally
    InterceptRemove(tr);
  end;
end;

procedure TRipDispTests.ImplicitEax_Mul;
var
  tr: Pointer;
begin
  GFactor := 7;
  tr := InterceptCreate(@MulByGlobal, @DummyMul);
  Assert.IsTrue(tr <> nil, 'no trampoline');
  try
    Assert.AreEqual(UInt32(42), TMulFunc(tr)(6),
      'scratch register clobbered the implicit EAX of MUL');
  finally
    InterceptRemove(tr);
  end;
end;

procedure TRipDispTests.ImplicitEax_CmpXchg;
var
  tr: Pointer;
begin
  GExchange := 11;
  tr := InterceptCreate(@CasGlobal, @DummyCas);
  Assert.IsTrue(tr <> nil, 'no trampoline');
  try
    TCasFunc(tr)(11, 99);        // comparand matches -> swap
    Assert.AreEqual(99, GExchange, 'CMPXCHG did not swap on match');
    TCasFunc(tr)(11, 123);       // no longer matches -> unchanged
    Assert.AreEqual(99, GExchange, 'CMPXCHG swapped on mismatch');
  finally
    InterceptRemove(tr);
  end;
end;

procedure TRipDispTests.OpcodeMap_Fpu;
var
  tr: Pointer;
begin
  GFpuIn := 4711;
  GFpuOut := 0;
  tr := InterceptCreate(@FpuRoundTrip, @DummyInt);
  Assert.IsTrue(tr <> nil, 'no trampoline');
  try
    Assert.AreEqual(4711, TIntFunc(tr)(), 'FPU escape byte counted wrong');
  finally
    InterceptRemove(tr);
  end;
end;

// The expected value is taken from the untouched function first, so the test
// compares against real behaviour instead of a hard coded magic number.
procedure CheckOpcodeMap(AFunc: Pointer; const AWhat: string);
var
  Expected: UInt32;
  tr: Pointer;
begin
  Expected := TU32Func(AFunc)();
  tr := InterceptCreate(AFunc, @DummyU32);
  Assert.IsTrue(tr <> nil, 'no trampoline for ' + AWhat);
  try
    Assert.AreEqual(Expected, TU32Func(tr)(), AWhat + ' was relocated wrongly');
  finally
    InterceptRemove(tr);
  end;
end;

procedure TRipDispTests.OpcodeMap_TwoByte;
begin
  CheckOpcodeMap(@TwoByteLoad, 'MOVZX [rip+d] (two-byte opcode)');
end;

procedure TRipDispTests.OpcodeMap_ThreeByte_MandatoryPrefix;
begin
  CheckOpcodeMap(@ThreeByteCrc, 'CRC32 [rip+d] (three-byte + mandatory prefix)');
end;

procedure TRipDispTests.OpcodeMap_Vex2;
begin
  CheckOpcodeMap(@VexTwoByteLoad, 'VMOVUPS [rip+d] (VEX2)');
end;

procedure TRipDispTests.OpcodeMap_Vex3;
begin
  CheckOpcodeMap(@VexThreeByteMul, 'VPMULLD [rip+d] (VEX3)');
end;

{ TPatchAreaTests }

procedure TPatchAreaTests.LoopIntoPatchArea_IsRefused;
begin
  Assert.WillRaise(
    procedure
    begin
      InterceptCreate(@LoopIntoPatchArea, @DummyInt);
    end,
    Exception,
    'a loop target inside the patch area must be refused, not patched');
end;

procedure TPatchAreaTests.LoopBeyondPatchArea_IsHooked;
var
  tr: Pointer;
begin
  tr := InterceptCreate(@LoopBeyondPatchArea, @DummyInt);
  Assert.IsTrue(tr <> nil, 'refused a target whose loop is past the patch');
  try
    Assert.AreEqual(16, TIntFunc(tr)(), 'relocated prologue misbehaves');
  finally
    InterceptRemove(tr);
  end;
end;

{ TImportThunkTests }

procedure TImportThunkTests.ImportThunk_IsRelocated;
var
  tr: Pointer;
begin
  // Sanity: the thunk forwards correctly before anyone touches it.
  Assert.AreEqual(4711, ImportThunk, 'thunk broken before hooking');

  tr := InterceptCreate(@ImportThunk, @DummyInt);
  Assert.IsTrue(tr <> nil, 'no trampoline for an import thunk');
  try
    // The hook belongs on the THUNK, not on whatever the slot happens to point
    // at right now. Following the indirect jump would silently redirect every
    // caller of the imported routine, process wide.
    Assert.AreEqual(0, ImportThunk, 'calling the thunk did not reach the hook');
    Assert.AreEqual(4711, ThunkTarget,
      'the imported routine itself was hooked - GetRoot followed JMP [slot]');
    Assert.AreEqual(4711, TIntFunc(tr)(),
      'relocated JMP [slot] does not reach the imported routine');
  finally
    InterceptRemove(tr);
  end;

  Assert.AreEqual(4711, ImportThunk, 'thunk broken after unhooking');
end;

{ TDecoderSizeTests }

function DecodedSize(const ABytes: array of Byte): Integer;
var
  Inst: TInstruction;
  Buf: array [0 .. 31] of Byte;
  i: Integer;
begin
  FillChar(Buf, SizeOf(Buf), $90);
  for i := 0 to High(ABytes) do
    Buf[i] := ABytes[i];
  FillChar(Inst, SizeOf(TInstruction), #00);
  Inst.Archi := {$IFDEF CPUX64}CPUX64{$ELSE}CPUX32{$ENDIF};
  Inst.Options := DecodeVex;
  Inst.Addr := @Buf[0];
  Inst.VirtualAddr := nil;
  Result := DecodeInst(@Inst);
end;

procedure TDecoderSizeTests.Moffs_OperandSizePrefix_DoesNotShrinkOffset;
begin
  // MOV moffs, (E)AX / MOV moffs, AX - the offset is an ADDRESS, so only the
  // $67 address-size prefix may change its width. $66 selects AX over EAX and
  // must leave the offset alone. Delphi emits the $66 form in System.Set8087CW.
{$IFDEF CPUX64}
  // 48 A3 <8 byte offset>          mov [moffs64], rax
  Assert.AreEqual(10, DecodedSize([$48, $A3, 1, 2, 3, 4, 5, 6, 7, 8]),
    'REX.W moffs64');
  // 66 48 A3 <8 byte offset>       mov [moffs64], ax (REX.W wins the operand)
  Assert.AreEqual(11, DecodedSize([$66, $48, $A3, 1, 2, 3, 4, 5, 6, 7, 8]),
    'operand-size prefix shrank the moffs offset');
  // 66 A3 <8 byte offset>          mov word ptr [moffs64], ax - no REX.W, so
  // the old code took vOpSize = 2 and reported 3 bytes instead of 10.
  Assert.AreEqual(10, DecodedSize([$66, $A3, 1, 2, 3, 4, 5, 6, 7, 8]),
    'operand-size prefix shrank the moffs offset (no REX.W)');
{$ELSE}
  // A3 <4 byte offset>             mov [moffs32], eax
  Assert.AreEqual(5, DecodedSize([$A3, $30, $90, $BF, $00]), 'plain moffs32');
  // 66 A3 <4 byte offset>          mov word ptr [moffs32], ax
  Assert.AreEqual(6, DecodedSize([$66, $A3, $30, $90, $BF, $00]),
    'operand-size prefix shrank the moffs offset');
{$ENDIF}
end;

initialization

TDUnitX.RegisterTestFixture(TRipDispTests);
TDUnitX.RegisterTestFixture(TPatchAreaTests);
TDUnitX.RegisterTestFixture(TImportThunkTests);
TDUnitX.RegisterTestFixture(TDecoderSizeTests);

end.
