program DecodeProbe;

(*
 * Instruction decoder probe for DDetours / InstDecode.
 *
 * Prints, for a sequence of instructions, everything that matters when the
 * hook engine relocates a prologue: length, opcode table, prefixes, ModRm,
 * displacement and immediate. A wrong InstSize here is what later shows up as
 * an access violation at a random address inside the trampoline, so this is
 * the first tool to reach for when a hook corrupts its target.
 *
 * Usage:
 *   DecodeProbe                 decode the built-in reference cases
 *   DecodeProbe 66 0F 38 40 05 11 22 33 44
 *                               decode an arbitrary byte sequence (hex)
 *
 * PITFALL: Inst.Options must contain DecodeVex, otherwise the decoder does not
 * understand VEX at all - it falls back to Decode_NA_ModRm and reports garbage
 * (a VEX instruction then decodes as several short bogus ones). DDetours sets
 * this itself (DDetours.pas, "PInst.Options := DecodeVex").
 *
 * Reference cases below are the ones that actually broke:
 *   SUB [rip+d],imm8   displacement followed by an immediate
 *   FILD [rip+d]       FPU escape byte + ModRm
 *   MOVZX [rip+d]      two-byte opcode ($0F xx)
 *   CRC32 [rip+d]      three-byte opcode ($0F $38 xx) WITH mandatory prefix
 *   VMOVUPS [rip+d]    two-byte VEX prefix ($C5)
 *   VPMULLD [rip+d]    three-byte VEX prefix ($C4)
 *)

{$APPTYPE CONSOLE}

uses
  Winapi.Windows,
  System.SysUtils,
  InstDecode;

var
  GCounter: Integer = 0;
  GFpuIn: Integer = 0;
  GByte: Byte = $AB;
  GCrcIn: UInt32 = $12345678;
  GVecA: array [0 .. 3] of UInt32 = (1, 2, 3, 4);
  GVecB: array [0 .. 3] of UInt32 = (5, 6, 7, 8);

// Reference snippets. Written in assembler so the interesting instruction is
// the first one - a Pascal function would start with its stack frame.
procedure SnipSubImm;
asm
{$IFDEF CPUX64}
  sub   dword ptr [rip + GCounter], 1
{$ELSE}
  sub   dword ptr [GCounter], 1
{$ENDIF}
end;

procedure SnipFpu;
asm
{$IFDEF CPUX64}
  fild  dword ptr [rip + GFpuIn]
{$ELSE}
  fild  dword ptr [GFpuIn]
{$ENDIF}
end;

procedure SnipTwoByte;
asm
{$IFDEF CPUX64}
  movzx eax, byte ptr [rip + GByte]
{$ELSE}
  movzx eax, byte ptr [GByte]
{$ENDIF}
end;

procedure SnipThreeByte;
asm
{$IFDEF CPUX64}
  crc32 eax, dword ptr [rip + GCrcIn]
{$ELSE}
  crc32 eax, dword ptr [GCrcIn]
{$ENDIF}
end;

procedure SnipVex2;
asm
{$IFDEF CPUX64}
  vmovups xmm0, [rip + GVecA]
{$ELSE}
  vmovups xmm0, [GVecA]
{$ENDIF}
end;

procedure SnipVex3;
asm
{$IFDEF CPUX64}
  vpmulld xmm0, xmm1, [rip + GVecB]
{$ELSE}
  vpmulld xmm0, xmm1, [GVecB]
{$ENDIF}
end;

function TableName(T: Byte): string;
begin
  case T of
    1: Result := 'OneByte';
    2: Result := 'TwoByte';
    3: Result := 'ThreeByte';
    4: Result := 'FPU';
  else
    Result := IntToStr(T);
  end;
end;

function VexName(Prefixes: Word): string;
begin
  // Prf_Vex2/Prf_Vex3 share the Prf_VEX bit - compare for equality, never <> 0
  if Prefixes and Prf_Vex3 = Prf_Vex3 then
    Result := 'VEX3'
  else if Prefixes and Prf_Vex2 = Prf_Vex2 then
    Result := 'VEX2'
  else
    Result := '-';
end;

procedure Dump(const AName: string; P: PByte; ACount: Integer);
var
  Inst: TInstruction;
  i, n: Integer;
  s: string;
begin
  Writeln(AName, ':');
  s := '';
  for i := 0 to 15 do
    s := s + IntToHex(PByte(NativeInt(P) + i)^, 2) + ' ';
  Writeln('  bytes : ', s);
  for n := 1 to ACount do
  begin
    FillChar(Inst, SizeOf(Inst), 0);
    Inst.Archi := {$IFDEF CPUX64}CPUX64{$ELSE}CPUX32{$ENDIF};
    Inst.Options := DecodeVex;      // <- without this VEX decodes as garbage
    Inst.Addr := P;
    Inst.VirtualAddr := P;
    Inst.NextInst := P;
    DecodeInst(@Inst);
    if Inst.InstSize <= 0 then
    begin
      Writeln('  #', n, ' : decoder returned size ', Inst.InstSize, ' - stopping');
      Break;
    end;
    Writeln(Format('  #%d size=%-2d table=%-9s vex=%-4s prefixes=$%.4x ' +
      'modrm=$%.2x disp(size=%d flags=$%.2x) imm(size=%d flags=$%.2x) err=%d',
      [n, Inst.InstSize, TableName(Inst.OpTable), VexName(Inst.Prefixes),
       Inst.Prefixes, Inst.ModRm.Value, Inst.Disp.Size, Inst.Disp.Flags,
       Inst.Imm.Size, Inst.Imm.Flags, Inst.Errors]));
    P := PByte(NativeInt(P) + Inst.InstSize);
  end;
  Writeln;
end;

// Decode a byte sequence given on the command line, e.g.
//   DecodeProbe F2 0F 38 F1 05 11 22 33 44
var
  Buf: array [0 .. 63] of Byte;

procedure DumpFromCmdLine;
var
  i, n: Integer;
  b: Integer;
begin
  FillChar(Buf, SizeOf(Buf), $90);
  n := 0;
  for i := 1 to ParamCount do
  begin
    if n > High(Buf) then
      Break;
    b := StrToIntDef('$' + ParamStr(i), -1);
    if (b < 0) or (b > 255) then
    begin
      Writeln('not a hex byte: ', ParamStr(i));
      Halt(1);
    end;
    Buf[n] := Byte(b);
    Inc(n);
  end;
  Dump(Format('command line (%d bytes)', [n]), @Buf[0], 4);
end;

begin
  Writeln('DecodeProbe - ', {$IFDEF CPUX64}'x64'{$ELSE}'Win32'{$ENDIF});
  Writeln;
  try
    if ParamCount > 0 then
      DumpFromCmdLine
    else
    begin
      Dump('SUB [rip+d],imm8  (disp followed by immediate)', @SnipSubImm, 1);
      Dump('FILD [rip+d]      (FPU escape + ModRm)',         @SnipFpu, 1);
      Dump('MOVZX [rip+d]     (two-byte opcode)',            @SnipTwoByte, 1);
      Dump('CRC32 [rip+d]     (three-byte + mandatory prf)', @SnipThreeByte, 1);
      Dump('VMOVUPS [rip+d]   (VEX2 prefix)',                @SnipVex2, 1);
      Dump('VPMULLD [rip+d]   (VEX3 prefix)',                @SnipVex3, 1);
    end;
  except
    on E: Exception do
      Writeln('EXCEPTION: ', E.ClassName, ': ', E.Message);
  end;
end.
