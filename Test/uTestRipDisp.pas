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

implementation

uses
  DDetours;

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

initialization

TDUnitX.RegisterTestFixture(TRipDispTests);

end.
