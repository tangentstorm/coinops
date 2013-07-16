{$mode objfpc}
program sha256_mjw;
uses sysutils, dateutils;
  
type
  T256BitDigest = record
    case integer of
      0 : (Longs : array[0..7] of LongWord);
      1 : (Words : array[0..15] of Word);
      2 : (Bytes : array[0..31] of Byte);
    end;
  

  type
  T512BitBuf = array[0..63] of Byte;

{                                                                              }
{ ReverseMem                                                                   }
{ Utility function to reverse order of data in buffer.                         }
{                                                                              }
procedure ReverseMem(var Buf; const BufSize: Integer);
var I : Integer;
    P : PByte;
    Q : PByte;
    T : Byte;
begin
  P := @Buf;
  Q := P;
  Inc(Q, BufSize - 1);
  for I := 1 to BufSize div 2 do
    begin
      T := P^;
      P^ := Q^;
      Q^ := T;
      Inc(P);
      Dec(Q);
    end;
end;


    
{                                                                              }
{ StdFinalBuf                                                                  }
{ Utility function to prepare final buffer(s).                                 }
{ Fills Buf1 and potentially Buf2 from Buf (FinalBufCount = 1 or 2).           }
{ Used by MD5, SHA1, SHA256, SHA512.                                           }
{                                                                              }
procedure StdFinalBuf512(
          const Buf; const BufSize: Integer; const TotalSize: Int64;
          var Buf1, Buf2: T512BitBuf;
          var FinalBufs: Integer;
          const SwapEndian: Boolean);
var P, Q : PByte;
    I : Integer;
    L : Int64;
begin
  Assert(BufSize < 64, 'Final BufSize must be less than 64 bytes');
  Assert(TotalSize >= BufSize, 'TotalSize >= BufSize');

  P := @Buf;
  Q := @Buf1[0];
  if BufSize > 0 then
    begin
      Move(P^, Q^, BufSize);
      Inc(Q, BufSize);
    end;
  Q^ := $80;
  Inc(Q);

  {$IFDEF DELPHI5}
  // Delphi 5 sometimes reports fatal error (internal error C1093) when compiling:
  //   L := TotalSize * 8
  L := TotalSize;
  L := L * 8;
  {$ELSE}
  L := TotalSize * 8;
  {$ENDIF}
  if SwapEndian then
    ReverseMem(L, 8);
  if BufSize + 1 > 64 - Sizeof(Int64) then
    begin
      FillChar(Q^, 64 - BufSize - 1, #0);
      Q := @Buf2[0];
      FillChar(Q^, 64 - Sizeof(Int64), #0);
      Inc(Q, 64 - Sizeof(Int64));
      PInt64(Q)^ := L;
      FinalBufs := 2;
    end
  else
    begin
      I := 64 - Sizeof(Int64) - BufSize - 1;
      FillChar(Q^, I, #0);
      Inc(Q, I);
      PInt64(Q)^ := L;
      FinalBufs := 1;
    end;
end;


{                                                                              }
{ Digests                                                                      }
{                                                                              }
const
  s_HexDigitsLower : String[16] = '0123456789abcdef';

procedure DigestToHexBufA(const Digest; const Size: Integer; const Buf);
var I : Integer;
    P : PAnsiChar;
    Q : PByte;
begin
  P := @Buf;;
  Assert(Assigned(P));
  Q := @Digest;
  Assert(Assigned(Q));
  for I := 0 to Size - 1 do
    begin
      P^ := s_HexDigitsLower[Q^ shr 4 + 1];
      Inc(P);
      P^ := s_HexDigitsLower[Q^ and 15 + 1];
      Inc(P);
      Inc(Q);
    end;
end;

function DigestToHexA(const Digest; const Size: Integer): AnsiString;
begin
  SetLength(Result, Size * 2);          
  DigestToHexBufA(Digest, Size, Pointer(Result)^);
end;

  procedure SwapEndianBuf(var Buf; const Count: Integer);
var P : PLongWord;
    I : Integer;
begin
  P := @Buf;
  for I := 1 to Count do
    begin
      P^ := SwapEndian(P^);
      Inc(P);
    end;
end;

{                                                                              }
{ Secure memory clear                                                          }
{                                                                              }
procedure SecureClear(var Buf; const BufSize: Integer);
begin
  if BufSize <= 0 then
    exit;
  FillChar(Buf, BufSize, #$00);
end;

procedure SecureClear512(var Buf: T512BitBuf);
begin
  SecureClear(Buf, SizeOf(Buf));
end;

{$IFDEF ASM386_DELPHI}
function RotateLeftBits(const Value: LongWord; const Bits: Byte): LongWord;
asm
      MOV     CL, DL
      ROL     EAX, CL
end;
{$ELSE}
function RotateLeftBits(const Value: LongWord; const Bits: Byte): LongWord;
var I : Integer;
    R : LongWord;
begin
  R := Value;
  for I := 1 to Bits do
    if R and $80000000 = 0 then
      R := LongWord(R shl 1)
    else
      R := LongWord(R shl 1) or 1;
  Result := R;
end;
{$ENDIF}

{$IFDEF ASM386_DELPHI}
function RotateRightBits(const Value: LongWord; const Bits: Byte): LongWord;
asm
      MOV     CL, DL
      ROR     EAX, CL
end;
{$ELSE}
function RotateRightBits(const Value: LongWord; const Bits: Byte): LongWord;
var I, B : Integer;
begin
  Result := Value;
  if Bits >= 32 then
    B := Bits mod 32
  else
    B := Bits;
  for I := 1 to B do
    if Result and 1 = 0 then
      Result := Result shr 1
    else
      Result := (Result shr 1) or $80000000;
end;
{$ENDIF}




{                                                                              }
{ SHA256 hashing                                                               }
{                                                                              }
procedure SHA256InitDigest(var Digest: T256BitDigest);
begin
  Digest.Longs[0] := $6a09e667;
  Digest.Longs[1] := $bb67ae85;
  Digest.Longs[2] := $3c6ef372;
  Digest.Longs[3] := $a54ff53a;
  Digest.Longs[4] := $510e527f;
  Digest.Longs[5] := $9b05688c;
  Digest.Longs[6] := $1f83d9ab;
  Digest.Longs[7] := $5be0cd19;
end;

function SHA256Transform1(const A: LongWord): LongWord;
begin
  Result := RotateRightBits(A, 7) xor RotateRightBits(A, 18) xor (A shr 3);
end;

function SHA256Transform2(const A: LongWord): LongWord;
begin
  Result := RotateRightBits(A, 17) xor RotateRightBits(A, 19) xor (A shr 10);
end;

function SHA256Transform3(const A: LongWord): LongWord;
begin
  Result := RotateRightBits(A, 2) xor RotateRightBits(A, 13) xor RotateRightBits(A, 22);
end;

function SHA256Transform4(const A: LongWord): LongWord;
begin
  Result := RotateRightBits(A, 6) xor RotateRightBits(A, 11) xor RotateRightBits(A, 25);
end;

const
  // first 32 bits of the fractional parts of the cube roots of the first 64 primes 2..311
  SHA256K: array[0..63] of LongWord = (
    $428a2f98, $71374491, $b5c0fbcf, $e9b5dba5, $3956c25b, $59f111f1, $923f82a4, $ab1c5ed5,
    $d807aa98, $12835b01, $243185be, $550c7dc3, $72be5d74, $80deb1fe, $9bdc06a7, $c19bf174,
    $e49b69c1, $efbe4786, $0fc19dc6, $240ca1cc, $2de92c6f, $4a7484aa, $5cb0a9dc, $76f988da,
    $983e5152, $a831c66d, $b00327c8, $bf597fc7, $c6e00bf3, $d5a79147, $06ca6351, $14292967,
    $27b70a85, $2e1b2138, $4d2c6dfc, $53380d13, $650a7354, $766a0abb, $81c2c92e, $92722c85,
    $a2bfe8a1, $a81a664b, $c24b8b70, $c76c51a3, $d192e819, $d6990624, $f40e3585, $106aa070,
    $19a4c116, $1e376c08, $2748774c, $34b0bcb5, $391c0cb3, $4ed8aa4a, $5b9cca4f, $682e6ff3,
    $748f82ee, $78a5636f, $84c87814, $8cc70208, $90befffa, $a4506ceb, $bef9a3f7, $c67178f2
  );

procedure TransformSHA256Buffer(var Digest: T256BitDigest; const Buf);
var
  I : Integer;
  W : array[0..63] of LongWord;
  P : PLongWord;
  S0, S1, Maj, T1, T2, Ch : LongWord;
  H : array[0..7] of LongWord;
begin
  P := @Buf;
  for I := 0 to 15 do
    begin
      W[I] := SwapEndian(P^);
      Inc(P);
    end;
  for I := 16 to 63 do
    begin
      S0 := SHA256Transform1(W[I - 15]);
      S1 := SHA256Transform2(W[I - 2]);
      W[I] := W[I - 16] + S0 + W[I - 7] + S1;
    end;
  for I := 0 to 7 do
    H[I] := Digest.Longs[I];
  for I := 0 to 63 do
    begin
      S0 := SHA256Transform3(H[0]);
      Maj := (H[0] and H[1]) xor (H[0] and H[2]) xor (H[1] and H[2]);
      T2 := S0 + Maj;
      S1 := SHA256Transform4(H[4]);
      Ch := (H[4] and H[5]) xor ((not H[4]) and H[6]);
      T1 := H[7] + S1 + Ch + SHA256K[I] + W[I];
      H[7] := H[6];
      H[6] := H[5];
      H[5] := H[4];
      H[4] := H[3] + T1;
      H[3] := H[2];
      H[2] := H[1];
      H[1] := H[0];
      H[0] := T1 + T2;
    end;
  for I := 0 to 7 do
    Inc(Digest.Longs[I], H[I]);
end;

procedure SHA256Buf(var Digest: T256BitDigest; const Buf; const BufSize: Integer);
var P : PByte;
    I, J : Integer;
begin
  I := BufSize;
  if I <= 0 then
    exit;
  Assert(I mod 64 = 0, 'BufSize must be multiple of 64 bytes');
  P := @Buf;
  for J := 0 to I div 64 - 1 do
    begin
      TransformSHA256Buffer(Digest, P^);
      Inc(P, 64);
    end;
end;

procedure SHA256FinalBuf(var Digest: T256BitDigest; const Buf; const BufSize: Integer; const TotalSize: Int64);
var B1, B2 : T512BitBuf;
    C : Integer;
begin
  StdFinalBuf512(Buf, BufSize, TotalSize, B1, B2, C, True);
  TransformSHA256Buffer(Digest, B1);
  if C > 1 then
    TransformSHA256Buffer(Digest, B2);
  SwapEndianBuf(Digest, Sizeof(Digest) div Sizeof(LongWord));
  SecureClear512(B1);
  if C > 1 then
    SecureClear512(B2);
end;

function CalcSHA256(const Buf; const BufSize: Integer): T256BitDigest;
var I, J : Integer;
    P    : PByte;
begin
  SHA256InitDigest(Result);
  P := @Buf;
  if BufSize <= 0 then
    I := 0 else
    I := BufSize;
  J := (I div 64) * 64;
  if J > 0 then
    begin
      SHA256Buf(Result, P^, J);
      Inc(P, J);
      Dec(I, J);
    end;
  SHA256FinalBuf(Result, P^, I, BufSize);
end;

function CalcSHA256(const Buf: AnsiString): T256BitDigest;
begin
  Result := CalcSHA256(Pointer(Buf)^, Length(Buf));
end;

function SHA256DigestToHexA(const Digest: T256BitDigest): AnsiString;
begin
  Result := DigestToHexA(Digest, Sizeof(Digest));
end;

 
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
  writeln(SHA256DigestToHexA(d));
end.


  
{******************************************************************************}
{                                                                              }
{   Library:          Fundamentals 4.00                                        }
{   File name:        cHash.pas                                                }
{   File version:     4.18                                                     }
{   Description:      Hashing functions                                        }
{                                                                              }
{   Copyright:        Copyright (c) 1999-2013, David J Butler                  }
{                     All rights reserved.                                     }
{                     Redistribution and use in source and binary forms, with  }
{                     or without modification, are permitted provided that     }
{                     the following conditions are met:                        }
{                     Redistributions of source code must retain the above     }
{                     copyright notice, this list of conditions and the        }
{                     following disclaimer.                                    }
{                     THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND   }
{                     CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED          }
{                     WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED   }
{                     WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A          }
{                     PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL     }
{                     THE REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT,    }
{                     INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR             }
{                     CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,    }
{                     PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF     }
{                     USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)         }
{                     HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER   }
{                     IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING        }
{                     NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE   }
{                     USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE             }
{                     POSSIBILITY OF SUCH DAMAGE.                              }
{                                                                              }
{   Home page:        http://fundementals.sourceforge.net                      }
{   Forum:            http://sourceforge.net/forum/forum.php?forum_id=2117     }
{   E-mail:           fundamentals.library@gmail.com                           }
