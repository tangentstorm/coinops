NB. SHA-256 implementation(s) in J
NB. Copyright © 2015 Michal J Wallace <http://tangentstorm.com/>
NB. Available for use under the MIT/X11 License.
NB. ==========================================================================

NB. these are the basic operations we use.
V=: 23 b.             NB. bitwise or
X=: 22 b.             NB. bitwise xor
A=: 17 b.             NB. bitwise and
LT=: 20 b.            NB. bitwise less than ("not x, but y")
P=: 16bffffffff A +   NB. 32 bit unsigned addition
LSH=: 33 b.           NB. eg: 1 2 LSH 8 -> 16 32
RSH=: -@[ 33 b. ]     NB. eg: 1 2 RSH 8 -> 4 2
bit=: (-@[ {. #:@])"0

NB. R is an operation that rotates the bits of uint32 y rightward by x bits
NB. it is the primitive instruction 'ROR' on intel cpus
NB. 32 b. is left rotate in j, but 64-bit on 64-bit machines.
NB. R :: u5 -> u32 -> u32
NB. ==========================================================================
R =: [: : ([: #. -@[ |. (32 bit ]))f. "0 1

NB. XR xors the result of multiple rotations of y
NB. XR :: u5[i] -> u32 -> u32
NB. ==========================================================================
XR =: [: X/ R


NB. k : constants based on fractional part of cube root of first 64 primes
NB. ==========================================================================
K=:   16b428a2f98 16b71374491 16bb5c0fbcf 16be9b5dba5
K=:K, 16b3956c25b 16b59f111f1 16b923f82a4 16bab1c5ed5
K=:K, 16bd807aa98 16b12835b01 16b243185be 16b550c7dc3
K=:K, 16b72be5d74 16b80deb1fe 16b9bdc06a7 16bc19bf174
K=:K, 16be49b69c1 16befbe4786 16b0fc19dc6 16b240ca1cc
K=:K, 16b2de92c6f 16b4a7484aa 16b5cb0a9dc 16b76f988da
K=:K, 16b983e5152 16ba831c66d 16bb00327c8 16bbf597fc7
K=:K, 16bc6e00bf3 16bd5a79147 16b06ca6351 16b14292967
K=:K, 16b27b70a85 16b2e1b2138 16b4d2c6dfc 16b53380d13
K=:K, 16b650a7354 16b766a0abb 16b81c2c92e 16b92722c85
K=:K, 16ba2bfe8a1 16ba81a664b 16bc24b8b70 16bc76c51a3
K=:K, 16bd192e819 16bd6990624 16bf40e3585 16b106aa070
K=:K, 16b19a4c116 16b1e376c08 16b2748774c 16b34b0bcb5
K=:K, 16b391c0cb3 16b4ed8aa4a 16b5b9cca4f 16b682e6ff3
K=:K, 16b748f82ee 16b78a5636f 16b84c87814 16b8cc70208
K=:K, 16b90befffa 16ba4506ceb 16bbef9a3f7 16bc67178f2

NB. H0 (initial hash): fractional part of square root of the first 8 primes
NB. ==========================================================================
H0=:   16b6a09e667 16bbb67ae85 16b3c6ef372 16ba54ff53a
H0=:H0,16b510e527f 16b9b05688c 16b1f83d9ab 16b5be0cd19

NB. W :: u32[16] -> u32[64]
NB. ==========================================================================
NB. the first 16 entries are simply y

sig0 =: verb : 'X/ ( 7 18 R y),  3 RSH y'
sig1 =: verb : 'X/ (17 19 R y), 10 RSH y'

ch =: verb define
  (a A b) X (a LT c) [ 'a b c'=. y
)

maj =: verb define
  X/ (a A b), (a A c), (b A c) [ 'a b c'=. y
)

W =: verb define
  w =. (i.16) { y
  NB. these are scrambled to create the other 48 entries.
  NB. note that referencing (ii - 2){w  makes this an
  NB. inherently sequential process.
  for_i. 16 + i.48 do.
    'wa wb wc wd' =. (i - 2 7 15 16) { w
    w =. w, P/ wd, (sig0 wc), wb, (sig1 wa)
  end.
)

blocks =: verb define
  'input should be a bit vector' assert 'boolean' -: datatype y
  pad =. 512 | 448 - 1 + # y  NB. 1 extra bit because of end marker.
  _16 [\ _32 #.\ y, 1, (pad # 0), 64 bit # y
)


NB. sha256 :: u32[16] -> u32[16]
NB. ==========================================================================

sum0 =: 2 13 22 XR ]
sum1 =: 6 11 25 XR ]

NB. version 1: straightforward, imperative loop
NB. --------------------------------------------------------------------------
compress =: dyad define
  'a b c d e f g h' =. x [ w =. W y
  for_i. i.64 do.
    t1 =. P/ h, (sum1 e), (ch e,f,g), (i{K), (i{w)
    t2 =. P/ (sum0 a), (maj a,b,c)
    'a b c d e f g h' =. (t1 P t2), a, b, c, (d P t1), e, f, g
  end.
)

sha256v1 =: verb define
  r =. H0 for_b. blocks y do. r =. r P r compress b end.
)


NB. version 2: explicit unrolled loop
NB. --------------------------------------------------------------------------
NB. this leaves most of the data in place at each step, eliminating
NB. a bunch of useless copying of unchanged values.
NB. (we will fix the horrendous duplication in the next version)
T1 =: verb define
  'e f g h ki wi' =. y
  t1 =. P/ h, (sum1 e), (ch e,f,g), ki, wi
)

T2 =: verb define
  'a b c' =. y
  t2 =. P/ (sum0 a), (maj a,b,c)
)

sha256v2 =: verb define
  r =. H0
  for_block. blocks y do. w =. W block [ 'a b c d e f g h' =. r

    d=.d P t1 [h=.t1 P t2 [t2=.T2 a,b,c [t1=.T1 e,f,g,h,16b428a2f98, 0{w
    c=.c P t1 [g=.t1 P t2 [t2=.T2 h,a,b [t1=.T1 d,e,f,g,16b71374491, 1{w
    b=.b P t1 [f=.t1 P t2 [t2=.T2 g,h,a [t1=.T1 c,d,e,f,16bb5c0fbcf, 2{w
    a=.a P t1 [e=.t1 P t2 [t2=.T2 f,g,h [t1=.T1 b,c,d,e,16be9b5dba5, 3{w
    h=.h P t1 [d=.t1 P t2 [t2=.T2 e,f,g [t1=.T1 a,b,c,d,16b3956c25b, 4{w
    g=.g P t1 [c=.t1 P t2 [t2=.T2 d,e,f [t1=.T1 h,a,b,c,16b59f111f1, 5{w
    f=.f P t1 [b=.t1 P t2 [t2=.T2 c,d,e [t1=.T1 g,h,a,b,16b923f82a4, 6{w
    e=.e P t1 [a=.t1 P t2 [t2=.T2 b,c,d [t1=.T1 f,g,h,a,16bab1c5ed5, 7{w
    d=.d P t1 [h=.t1 P t2 [t2=.T2 a,b,c [t1=.T1 e,f,g,h,16bd807aa98, 8{w
    c=.c P t1 [g=.t1 P t2 [t2=.T2 h,a,b [t1=.T1 d,e,f,g,16b12835b01, 9{w
    b=.b P t1 [f=.t1 P t2 [t2=.T2 g,h,a [t1=.T1 c,d,e,f,16b243185be,10{w
    a=.a P t1 [e=.t1 P t2 [t2=.T2 f,g,h [t1=.T1 b,c,d,e,16b550c7dc3,11{w
    h=.h P t1 [d=.t1 P t2 [t2=.T2 e,f,g [t1=.T1 a,b,c,d,16b72be5d74,12{w
    g=.g P t1 [c=.t1 P t2 [t2=.T2 d,e,f [t1=.T1 h,a,b,c,16b80deb1fe,13{w
    f=.f P t1 [b=.t1 P t2 [t2=.T2 c,d,e [t1=.T1 g,h,a,b,16b9bdc06a7,14{w
    e=.e P t1 [a=.t1 P t2 [t2=.T2 b,c,d [t1=.T1 f,g,h,a,16bc19bf174,15{w

    d=.d P t1 [h=.t1 P t2 [t2=.T2 a,b,c [t1=.T1 e,f,g,h,16be49b69c1,16{w
    c=.c P t1 [g=.t1 P t2 [t2=.T2 h,a,b [t1=.T1 d,e,f,g,16befbe4786,17{w
    b=.b P t1 [f=.t1 P t2 [t2=.T2 g,h,a [t1=.T1 c,d,e,f,16b0fc19dc6,18{w
    a=.a P t1 [e=.t1 P t2 [t2=.T2 f,g,h [t1=.T1 b,c,d,e,16b240ca1cc,19{w
    h=.h P t1 [d=.t1 P t2 [t2=.T2 e,f,g [t1=.T1 a,b,c,d,16b2de92c6f,20{w
    g=.g P t1 [c=.t1 P t2 [t2=.T2 d,e,f [t1=.T1 h,a,b,c,16b4a7484aa,21{w
    f=.f P t1 [b=.t1 P t2 [t2=.T2 c,d,e [t1=.T1 g,h,a,b,16b5cb0a9dc,22{w
    e=.e P t1 [a=.t1 P t2 [t2=.T2 b,c,d [t1=.T1 f,g,h,a,16b76f988da,23{w
    d=.d P t1 [h=.t1 P t2 [t2=.T2 a,b,c [t1=.T1 e,f,g,h,16b983e5152,24{w
    c=.c P t1 [g=.t1 P t2 [t2=.T2 h,a,b [t1=.T1 d,e,f,g,16ba831c66d,25{w
    b=.b P t1 [f=.t1 P t2 [t2=.T2 g,h,a [t1=.T1 c,d,e,f,16bb00327c8,26{w
    a=.a P t1 [e=.t1 P t2 [t2=.T2 f,g,h [t1=.T1 b,c,d,e,16bbf597fc7,27{w
    h=.h P t1 [d=.t1 P t2 [t2=.T2 e,f,g [t1=.T1 a,b,c,d,16bc6e00bf3,28{w
    g=.g P t1 [c=.t1 P t2 [t2=.T2 d,e,f [t1=.T1 h,a,b,c,16bd5a79147,29{w
    f=.f P t1 [b=.t1 P t2 [t2=.T2 c,d,e [t1=.T1 g,h,a,b,16b06ca6351,30{w
    e=.e P t1 [a=.t1 P t2 [t2=.T2 b,c,d [t1=.T1 f,g,h,a,16b14292967,31{w

    d=.d P t1 [h=.t1 P t2 [t2=.T2 a,b,c [t1=.T1 e,f,g,h,16b27b70a85,32{w
    c=.c P t1 [g=.t1 P t2 [t2=.T2 h,a,b [t1=.T1 d,e,f,g,16b2e1b2138,33{w
    b=.b P t1 [f=.t1 P t2 [t2=.T2 g,h,a [t1=.T1 c,d,e,f,16b4d2c6dfc,34{w
    a=.a P t1 [e=.t1 P t2 [t2=.T2 f,g,h [t1=.T1 b,c,d,e,16b53380d13,35{w
    h=.h P t1 [d=.t1 P t2 [t2=.T2 e,f,g [t1=.T1 a,b,c,d,16b650a7354,36{w
    g=.g P t1 [c=.t1 P t2 [t2=.T2 d,e,f [t1=.T1 h,a,b,c,16b766a0abb,37{w
    f=.f P t1 [b=.t1 P t2 [t2=.T2 c,d,e [t1=.T1 g,h,a,b,16b81c2c92e,38{w
    e=.e P t1 [a=.t1 P t2 [t2=.T2 b,c,d [t1=.T1 f,g,h,a,16b92722c85,39{w
    d=.d P t1 [h=.t1 P t2 [t2=.T2 a,b,c [t1=.T1 e,f,g,h,16ba2bfe8a1,40{w
    c=.c P t1 [g=.t1 P t2 [t2=.T2 h,a,b [t1=.T1 d,e,f,g,16ba81a664b,41{w
    b=.b P t1 [f=.t1 P t2 [t2=.T2 g,h,a [t1=.T1 c,d,e,f,16bc24b8b70,42{w
    a=.a P t1 [e=.t1 P t2 [t2=.T2 f,g,h [t1=.T1 b,c,d,e,16bc76c51a3,43{w
    h=.h P t1 [d=.t1 P t2 [t2=.T2 e,f,g [t1=.T1 a,b,c,d,16bd192e819,44{w
    g=.g P t1 [c=.t1 P t2 [t2=.T2 d,e,f [t1=.T1 h,a,b,c,16bd6990624,45{w
    f=.f P t1 [b=.t1 P t2 [t2=.T2 c,d,e [t1=.T1 g,h,a,b,16bf40e3585,46{w
    e=.e P t1 [a=.t1 P t2 [t2=.T2 b,c,d [t1=.T1 f,g,h,a,16b106aa070,47{w

    d=.d P t1 [h=.t1 P t2 [t2=.T2 a,b,c [t1=.T1 e,f,g,h,16b19a4c116,48{w
    c=.c P t1 [g=.t1 P t2 [t2=.T2 h,a,b [t1=.T1 d,e,f,g,16b1e376c08,49{w
    b=.b P t1 [f=.t1 P t2 [t2=.T2 g,h,a [t1=.T1 c,d,e,f,16b2748774c,50{w
    a=.a P t1 [e=.t1 P t2 [t2=.T2 f,g,h [t1=.T1 b,c,d,e,16b34b0bcb5,51{w
    h=.h P t1 [d=.t1 P t2 [t2=.T2 e,f,g [t1=.T1 a,b,c,d,16b391c0cb3,52{w
    g=.g P t1 [c=.t1 P t2 [t2=.T2 d,e,f [t1=.T1 h,a,b,c,16b4ed8aa4a,53{w
    f=.f P t1 [b=.t1 P t2 [t2=.T2 c,d,e [t1=.T1 g,h,a,b,16b5b9cca4f,54{w
    e=.e P t1 [a=.t1 P t2 [t2=.T2 b,c,d [t1=.T1 f,g,h,a,16b682e6ff3,55{w
    d=.d P t1 [h=.t1 P t2 [t2=.T2 a,b,c [t1=.T1 e,f,g,h,16b748f82ee,56{w
    c=.c P t1 [g=.t1 P t2 [t2=.T2 h,a,b [t1=.T1 d,e,f,g,16b78a5636f,57{w
    b=.b P t1 [f=.t1 P t2 [t2=.T2 g,h,a [t1=.T1 c,d,e,f,16b84c87814,58{w
    a=.a P t1 [e=.t1 P t2 [t2=.T2 f,g,h [t1=.T1 b,c,d,e,16b8cc70208,59{w
    h=.h P t1 [d=.t1 P t2 [t2=.T2 e,f,g [t1=.T1 a,b,c,d,16b90befffa,60{w
    g=.g P t1 [c=.t1 P t2 [t2=.T2 d,e,f [t1=.T1 h,a,b,c,16ba4506ceb,61{w
    f=.f P t1 [b=.t1 P t2 [t2=.T2 c,d,e [t1=.T1 g,h,a,b,16bbef9a3f7,62{w
    e=.e P t1 [a=.t1 P t2 [t2=.T2 b,c,d [t1=.T1 f,g,h,a,16bc67178f2,63{w
    r=.r P a,b,c,d,e,f,g,h
  end.
)



NB. version 3 : loop unrolling via meta-programming
NB. --------------------------------------------------------------------------

NB. hex parsing/formatting routines, for the constants
NB. there is no particular reason the constants taken from k have to be in hex,
NB. but i think the generated code looks nicer when everything is the same length.
hexcode =: ,{;~ '0123456789abcdef'      NB. :: s2[256]  (where s2 :: ch[2])
u8hex   =: [: > hexcode {~ ]                      NB. ::  u8 -> s2
hexu8   =: (hexcode i. <)                         NB. ::  s2 -> u8
u32hex  =: [: , [: u8hex f. 256 256 256 256 #: ]  NB. :: u32 -> s8
hex2int =: [: do '16b' , ]                        NB. :: str -> int


NB. sc (separate with commas) :: s -> s
sc =: ([: }. @: , ',' & (,"0/))

NB. macro to generate one step of the unrolled loop.
NB. example:  0 v3_macro 'abcdefgh'  produces the boxed string
NB. d=.(d P t1)[h=.(t1 P t2)[t2=.(T2 a,b,c)[t1=.(T1 e,f,g,h,16b428a2f98,0{w)
v3_macro =: 4 :0
  ii =. x [ 'a b c d e f g h' =. y
  r =. d, '=.(', d, ' P t1)'
  r =. r, '[',h,'=.(t1 P t2)'
  r =. r, '[t2=.(T2 ', (sc a,b,c), ')'
  r =. r, '[t1=.(T1 ', (sc e,f,g,h)
  r =. r, ',16b', (u32hex ii{K), ',', (":ii), '{w)'
  <r
)


NB. generate the code for the complete unrolled loop.
NB. result is a rank 2 arraf of shape (1 64),
NB. containing one boxed string for each line.
v3_unrolled =: ,. (i.64) v3_macro"0 1 ] _1|.^:(<64)'abcdefgh'

NB. finally, we just surround the generated code with lines
NB. for the initial setup and the return value, and then we
NB. can simply evaluate each generated line in the current scope.
sha256v3 =: 3 :0
  r =. H0
  for_block. blocks y do.
    w =. W block [ 'a b c d e f g h' =. r
    do each , v3_unrolled
    r =. r P a,b,c,d,e,f,g,h
  end.
)


NB. Test suite
hex32 =: ' ' joinstring every  _8 <\  [:(<"1)  _8 {.!.'0'"1 hfd

'a b c' =: 16b336699ff 16b12345678 16b01020304
assert  '9ff33669' -: hfd 12 R a
assert ('9947c186';'66146474') -: hfd@sum0 each a;b
assert ('7067092d';'3561abda') -: hfd@sum1 each a;b
assert ('5e75d2d5';'e7fce6ee') -: hfd@sig0 each a;b
assert ('9fcca679';'a1f78649') -: hfd@sig1 each a;b
assert ('12241278';'21428b87') -: hfd@ch each (a,b,c);(b,c,a)
assert ('1326137c';'1326137c') -: hfd@maj each (a,b,c);(b,c,a)

cheq hex32 0 { blocks 8$0
00800000 00000000 00000000 00000000 00000000 00000000 00000000 00000000
00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000008
)

cheq hex32 W 0 { blocks 8$0
00800000 00000000 00000000 00000000 00000000 00000000 00000000 00000000
00000000 00000000 00000000 00000000 00000000 00000000 00000000 00000008
00800000 00050000 00002050 20000142 14220008 00815400 4000001d 81002005
00220800 142250f8 650009d9 76880009 06503222 401837b2 b056f7f4 1d72762a
f9cbd695 82f01fad 883ed9ac c502018e 610d3a70 24279698 ab045a30 36661b24
9018b557 27788785 9265952c 731f4b9f 03feb174 7a548124 3f6fbeb9 3fa2e5ce
96794545 422369fe 0ad8025f 4550ba0a ae3342c2 10a73cb0 7c22d0d8 d72047b7
33e50097 8b8cc05f da6de127 5d7e919b c91ea2da 2b9e5421 be8d170e 1cd8fd4a
)

cheq hex32 sha256v1 8$0
6e340b9c ffb37a98 9ca544e6 bb780a2c 78901d3f b3373876 8511a306 17afa01d
)

cheq hex32 sha256v2 8$0
6e340b9c ffb37a98 9ca544e6 bb780a2c 78901d3f b3373876 8511a306 17afa01d
)

cheq hex32 sha256v3 8$0
6e340b9c ffb37a98 9ca544e6 bb780a2c 78901d3f b3373876 8511a306 17afa01d
)
