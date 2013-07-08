{$mode delphi}{$h+}
program sha256_dcp;
uses sysutils, dateutils, DCPcrypt2, DCPsha256, uSHA256;
  var i : integer; t : TDateTime; d : T256BitDigest;
  const
    s = '0123456789ABCDEF0123456789ABCDEF';
    n = 65536;

  function CalcSha256(s	: string) :  T256BitDigest; overload;
    var sha : TDCP_sha256;
    begin
      sha := TDCP_sha256.Create(nil);
      sha.Init;
      sha.UpdateStr(s);
      sha.Final(result);
      sha.Free;
    end;

  function CalcSha256(var buf; len : word ) :  T256BitDigest; overload;
    var sha : TDCP_sha256;
    begin
      sha := TDCP_sha256.Create(nil);
      sha.Init;
      sha.Update(buf, len);
      sha.Final(result);
      sha.Free;
    end;
  
begin
  t := now;
  d := CalcSHA256(s);
  for i := 2 to n do d := CalcSHA256(d, 32);
  writeln('recursively applied SHA256 to "', s, '" ', n, ' times in ',
	  Format('%0.3n',[MilliSecondsBetween( now, t )/1000]) : 3, 's.');
  writeln(SHA256DigestToHexW(d));
end.
