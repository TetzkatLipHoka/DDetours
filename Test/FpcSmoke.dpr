program FpcSmoke;

{ Free Pascal check for DDetours, see build_fpc.bat. The DUnitX suite does not
  build under FPC. Exit code 0 = all checks passed. }

{$IFDEF FPC}{$MODE DELPHI}{$ENDIF}
{$APPTYPE CONSOLE}
{$OPTIMIZATION OFF}

uses
  Windows, DDetours;

var
  Failed: Integer = 0;
  Sink: Integer = 0;

procedure Check(ACondition: Boolean; const AName: string);
begin
  if ACondition then
    Writeln('ok   ', AName)
  else
  begin
    Writeln('FAIL ', AName);
    Inc(Failed);
  end;
end;

function Target(A: Integer): Integer;
begin
  Inc(Sink);
  Result := A * 3 + Sink - Sink;
end;

function Replacement(A: Integer): Integer;
begin
  Result := A + 1000;
end;

var
  Trampoline: function(A: Integer): Integer = nil;

function Intercept(A: Integer): Integer;
begin
  Result := Trampoline(A) + 1;
end;

type
  TBase = class
    function Foo: Integer; virtual;
    function Bar: Integer; virtual;
  end;

function TBase.Foo: Integer;
begin
  Result := 1;
end;

function TBase.Bar: Integer;
begin
  Result := 2;
end;

function NewBar(Self: TObject): Integer;
begin
  Result := 22;
end;

function ImportedTick: DWORD; stdcall; external 'kernel32.dll' name 'GetTickCount';

function NewTick: DWORD; stdcall;
begin
  Result := 12345;
end;

var
  Backup: TXRedirCode;
  Obj: TBase;
  hKernel: HMODULE;
begin
  @Trampoline := InterceptCreate(@Target, @Intercept);
  Check(@Trampoline <> nil, 'InterceptCreate');
  Check(Target(2) = 7, 'intercepted call reaches the original');
  Check(InterceptRemove(@Trampoline) >= 0, 'InterceptRemove');
  Check(Target(2) = 6, 'original restored');

  HookProc(@Target, @Replacement, Backup);
  Check(Backup.Jump <> 0, 'HookProc');
  Check(Target(2) = 1002, 'HookProc replaces the function');
  UnhookProc(@Target, Backup);
  Check(Target(2) = 6, 'UnhookProc restores the function');

  Obj := TBase.Create;
  try
    ReplaceVmtField(TBase, @TBase.Bar, @NewBar);
    Check(Obj.Bar = 22, 'ReplaceVmtField swaps the entry');
    Check(Obj.Foo = 1, 'ReplaceVmtField leaves other entries alone');
  finally
    Obj.Free;
  end;

  ImportedTick;
  hKernel := GetModuleHandle('kernel32.dll');
  Check(HookImportFunctionAll(HInstance, 'kernel32.dll', GetProcAddress(hKernel, 'GetTickCount'), @NewTick) > 0,
    'HookImportFunctionAll finds the slot');
  Check(ImportedTick = 12345, 'HookImportFunctionAll redirects the import');

  Check(DDetoursPatchWrites > 0, 'DDetoursPatchWrites counts');

  if Failed = 0 then
    Writeln('RESULT: all checks passed')
  else
    Writeln('RESULT: ', Failed, ' FAILED');
  Halt(Failed);
end.
