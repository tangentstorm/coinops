{$mode delphi}{$h+}
program coinops;
uses uSHA256, sysutils, dateutils;
  var s : string; i : integer; t : TDateTime;
  const n = 32768;
begin
  s := 'hello world';
  t := now;
  for i := 1 to n do
    begin
      s := SHA256DigestToHexW(CALCSHA256(s));
    end;
  writeln('recursively applied SHA256 to "hello world" ', n, ' times in ',
	  Format('%0.3n',[MilliSecondsBetween( now, t )/1000]) : 3, 's.');
  writeln(s);
end.