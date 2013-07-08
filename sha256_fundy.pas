{$mode delphi}{$h+}
program coinops;
uses uSHA256, sysutils, dateutils;
  var i : integer; t : TDateTime; d : T256BitDigest;
  const
    s = '0123456789ABCDEF0123456789ABCDEF';
    n = 65536;
begin
  t := now;
  d := CalcSHA256(s);
  for i := 2 to n do d := CalcSHA256(d, 32);
  writeln('recursively applied SHA256 to "', s, '" ', n, ' times in ',
	  Format('%0.3n',[MilliSecondsBetween( now, t )/1000]) : 3, 's.');
  writeln(SHA256DigestToHexW(d));
end.
