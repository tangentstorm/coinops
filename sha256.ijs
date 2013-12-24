NB. SHA-256 implementation(s) in J
NB. ==========================================================================

NB. these are the basic operations we use.
V=. 23 b.             NB. bitwise or
X=. 22 b.             NB. bitwise xor
A=. 17 b.             NB. bitwise and
N=. 30 b.             NB. bitwise nand
G=.{~                 NB. a G i -> a[i]
P=. 16bffffffff A +   NB. 32 bit unsigned addition
LSH=. 33 b.           NB. eg: 1 2 LSH 8 -> 16 32
RSH=. -@:[ 33 b. ]    NB. eg: 1 2 RSH 8 -> 4 2

NB. R is an operation that rotates the bits of uint32 y rightward by x bits
NB. it is the primitive instruction 'ROR' on intel cpus
NB. R :: u5 -> u32 -> u32
NB. ==========================================================================
R =: 4 : 0
  NB. TODO: x (32 b.) y  is left rotate in j... try just:  -@:[ 32 b. ]
  (x RSH y) V ((32-x) LSH y)
)

NB. XR xors the result of multiple rotations of y
NB. XR :: u5[i] -> u32 -> u32
NB. ==========================================================================
XR =: 4 : 0
  X / x R y
)

NB. k is just an array of 64 constants
NB. ==========================================================================
k=:   16b428a2f98 16b71374491 16bb5c0fbcf 16be9b5dba5
k=:k, 16b3956c25b 16b59f111f1 16b923f82a4 16bab1c5ed5
k=:k, 16bd807aa98 16b12835b01 16b243185be 16b550c7dc3
k=:k, 16b72be5d74 16b80deb1fe 16b9bdc06a7 16bc19bf174
k=:k, 16be49b69c1 16befbe4786 16b0fc19dc6 16b240ca1cc
k=:k, 16b2de92c6f 16b4a7484aa 16b5cb0a9dc 16b76f988da
k=:k, 16b983e5152 16ba831c66d 16bb00327c8 16bbf597fc7
k=:k, 16bc6e00bf3 16bd5a79147 16b06ca6351 16b14292967
k=:k, 16b27b70a85 16b2e1b2138 16b4d2c6dfc 16b53380d13
k=:k, 16b650a7354 16b766a0abb 16b81c2c92e 16b92722c85
k=:k, 16ba2bfe8a1 16ba81a664b 16bc24b8b70 16bc76c51a3
k=:k, 16bd192e819 16bd6990624 16bf40e3585 16b106aa070
k=:k, 16b19a4c116 16b1e376c08 16b2748774c 16b34b0bcb5
k=:k, 16b391c0cb3 16b4ed8aa4a 16b5b9cca4f 16b682e6ff3
k=:k, 16b748f82ee 16b78a5636f 16b84c87814 16b8cc70208
k=:k, 16b90befffa 16ba4506ceb 16bbef9a3f7 16bc67178f2

NB. W :: u32[16] -> u32[64]
NB. ==========================================================================
NB. the first 16 entries are simply y
W =: 3 : 0
  w =. (i.16) { y
  NB. these are scrambled to create the other 48 entries.
  NB. note that referencing (ii - 2){w  makes this an
  NB. inherently sequential process.
  for_ii. 16 + i.48 do.
    'wa wb wc wd' =. (ii - 2 7 15 16) { w
    w =. w, ((17 19 10 XR wa) P wb P ((7&R X 18&R X 3&SHR) wc) P wd
  end.
)


NB. sha256 :: u32[16] -> u32[16]
NB. ==========================================================================


NB. version 1: straightforward, imperative loop
NB. --------------------------------------------------------------------------
sha256v1 =: 3 :0
  w =. W y
  'a b c d e f g h' =. (i. 8) { y
  for_ii. i. 64 do.
    t1 =. P/ h, ((6 11 25 & XR), (f &A X g &N) e), ((k&G , w&G) ii)
    t2 =. P/ (2 13 22 XR a), X/((b A c), b&A , c&A) a
    'a b c d e f g h' =. (t1 P t2), a, b, c, (d P t1), e, f, g
  end.
  a,b,c,d,e,f,g,h
)

NB. version 2: explicit unrolled loop
NB. --------------------------------------------------------------------------
NB. this leaves most of the data in place at each step, eliminating
NB. a bunch of useless copying of unchanged values.
NB. (we will fix the horrendous duplication in the next version)
T1 =: 3 :0
  'e f g h ki wi' =. y
  t1 =. P/ h, ((6 11 25 & XR), (f &A X g &N) e), ki, wi
)
T2 =: 3 :0
  'a b c' =. y
  t2 =. (2 13 22 XR a) P X/((b A c), b&A , c&A) a
)
sha256v2 =: 3 : 0
  w =. (W y) [ 'a b c d e f g h' =. (i. 8) { y
  d=.(d P t1) [h=.(t1 P t2) [t2=.(T2 a,b,c) [t1=.(T1 e,f,g,h,16b428a2f98, 0{w)
  c=.(c P t1) [g=.(t1 P t2) [t2=.(T2 h,a,b) [t1=.(T1 d,e,f,g,16b71374491, 1{w)
  b=.(b P t1) [f=.(t1 P t2) [t2=.(T2 g,h,a) [t1=.(T1 c,d,e,f,16bb5c0fbcf, 2{w)
  a=.(a P t1) [e=.(t1 P t2) [t2=.(T2 f,g,h) [t1=.(T1 b,c,d,e,16be9b5dba5, 3{w)
  h=.(h P t1) [d=.(t1 P t2) [t2=.(T2 e,f,g) [t1=.(T1 a,b,c,d,16b3956c25b, 4{w)
  g=.(g P t1) [c=.(t1 P t2) [t2=.(T2 d,e,f) [t1=.(T1 h,a,b,c,16b59f111f1, 5{w)
  f=.(f P t1) [b=.(t1 P t2) [t2=.(T2 c,d,e) [t1=.(T1 g,h,a,b,16b923f82a4, 6{w)
  e=.(e P t1) [a=.(t1 P t2) [t2=.(T2 b,c,d) [t1=.(T1 f,g,h,a,16bab1c5ed5, 7{w)
  d=.(d P t1) [h=.(t1 P t2) [t2=.(T2 a,b,c) [t1=.(T1 e,f,g,h,16bd807aa98, 8{w)
  c=.(c P t1) [g=.(t1 P t2) [t2=.(T2 h,a,b) [t1=.(T1 d,e,f,g,16b12835b01, 9{w)
  b=.(b P t1) [f=.(t1 P t2) [t2=.(T2 g,h,a) [t1=.(T1 c,d,e,f,16b243185be,10{w)
  a=.(a P t1) [e=.(t1 P t2) [t2=.(T2 f,g,h) [t1=.(T1 b,c,d,e,16b550c7dc3,11{w)
  h=.(h P t1) [d=.(t1 P t2) [t2=.(T2 e,f,g) [t1=.(T1 a,b,c,d,16b72be5d74,12{w)
  g=.(g P t1) [c=.(t1 P t2) [t2=.(T2 d,e,f) [t1=.(T1 h,a,b,c,16b80deb1fe,13{w)
  f=.(f P t1) [b=.(t1 P t2) [t2=.(T2 c,d,e) [t1=.(T1 g,h,a,b,16b9bdc06a7,14{w)
  e=.(e P t1) [a=.(t1 P t2) [t2=.(T2 b,c,d) [t1=.(T1 f,g,h,a,16bc19bf174,15{w)
  d=.(d P t1) [h=.(t1 P t2) [t2=.(T2 a,b,c) [t1=.(T1 e,f,g,h,16be49b69c1,16{w)
  c=.(c P t1) [g=.(t1 P t2) [t2=.(T2 h,a,b) [t1=.(T1 d,e,f,g,16befbe4786,17{w)
  b=.(b P t1) [f=.(t1 P t2) [t2=.(T2 g,h,a) [t1=.(T1 c,d,e,f,16b0fc19dc6,18{w)
  a=.(a P t1) [e=.(t1 P t2) [t2=.(T2 f,g,h) [t1=.(T1 b,c,d,e,16b240ca1cc,19{w)
  h=.(h P t1) [d=.(t1 P t2) [t2=.(T2 e,f,g) [t1=.(T1 a,b,c,d,16b2de92c6f,20{w)
  g=.(g P t1) [c=.(t1 P t2) [t2=.(T2 d,e,f) [t1=.(T1 h,a,b,c,16b4a7484aa,21{w)
  f=.(f P t1) [b=.(t1 P t2) [t2=.(T2 c,d,e) [t1=.(T1 g,h,a,b,16b5cb0a9dc,22{w)
  e=.(e P t1) [a=.(t1 P t2) [t2=.(T2 b,c,d) [t1=.(T1 f,g,h,a,16b76f988da,23{w)
  d=.(d P t1) [h=.(t1 P t2) [t2=.(T2 a,b,c) [t1=.(T1 e,f,g,h,16b983e5152,24{w)
  c=.(c P t1) [g=.(t1 P t2) [t2=.(T2 h,a,b) [t1=.(T1 d,e,f,g,16ba831c66d,25{w)
  b=.(b P t1) [f=.(t1 P t2) [t2=.(T2 g,h,a) [t1=.(T1 c,d,e,f,16bb00327c8,26{w)
  a=.(a P t1) [e=.(t1 P t2) [t2=.(T2 f,g,h) [t1=.(T1 b,c,d,e,16bbf597fc7,27{w)
  h=.(h P t1) [d=.(t1 P t2) [t2=.(T2 e,f,g) [t1=.(T1 a,b,c,d,16bc6e00bf3,28{w)
  g=.(g P t1) [c=.(t1 P t2) [t2=.(T2 d,e,f) [t1=.(T1 h,a,b,c,16bd5a79147,29{w)
  f=.(f P t1) [b=.(t1 P t2) [t2=.(T2 c,d,e) [t1=.(T1 g,h,a,b,16b06ca6351,30{w)
  e=.(e P t1) [a=.(t1 P t2) [t2=.(T2 b,c,d) [t1=.(T1 f,g,h,a,16b14292967,31{w)
  d=.(d P t1) [h=.(t1 P t2) [t2=.(T2 a,b,c) [t1=.(T1 e,f,g,h,16b27b70a85,32{w)
  c=.(c P t1) [g=.(t1 P t2) [t2=.(T2 h,a,b) [t1=.(T1 d,e,f,g,16b2e1b2138,33{w)
  b=.(b P t1) [f=.(t1 P t2) [t2=.(T2 g,h,a) [t1=.(T1 c,d,e,f,16b4d2c6dfc,34{w)
  a=.(a P t1) [e=.(t1 P t2) [t2=.(T2 f,g,h) [t1=.(T1 b,c,d,e,16b53380d13,35{w)
  h=.(h P t1) [d=.(t1 P t2) [t2=.(T2 e,f,g) [t1=.(T1 a,b,c,d,16b650a7354,36{w)
  g=.(g P t1) [c=.(t1 P t2) [t2=.(T2 d,e,f) [t1=.(T1 h,a,b,c,16b766a0abb,37{w)
  f=.(f P t1) [b=.(t1 P t2) [t2=.(T2 c,d,e) [t1=.(T1 g,h,a,b,16b81c2c92e,38{w)
  e=.(e P t1) [a=.(t1 P t2) [t2=.(T2 b,c,d) [t1=.(T1 f,g,h,a,16b92722c85,39{w)
  d=.(d P t1) [h=.(t1 P t2) [t2=.(T2 a,b,c) [t1=.(T1 e,f,g,h,16ba2bfe8a1,40{w)
  c=.(c P t1) [g=.(t1 P t2) [t2=.(T2 h,a,b) [t1=.(T1 d,e,f,g,16ba81a664b,41{w)
  b=.(b P t1) [f=.(t1 P t2) [t2=.(T2 g,h,a) [t1=.(T1 c,d,e,f,16bc24b8b70,42{w)
  a=.(a P t1) [e=.(t1 P t2) [t2=.(T2 f,g,h) [t1=.(T1 b,c,d,e,16bc76c51a3,43{w)
  h=.(h P t1) [d=.(t1 P t2) [t2=.(T2 e,f,g) [t1=.(T1 a,b,c,d,16bd192e819,44{w)
  g=.(g P t1) [c=.(t1 P t2) [t2=.(T2 d,e,f) [t1=.(T1 h,a,b,c,16bd6990624,45{w)
  f=.(f P t1) [b=.(t1 P t2) [t2=.(T2 c,d,e) [t1=.(T1 g,h,a,b,16bf40e3585,46{w)
  e=.(e P t1) [a=.(t1 P t2) [t2=.(T2 b,c,d) [t1=.(T1 f,g,h,a,16b106aa070,47{w)
  d=.(d P t1) [h=.(t1 P t2) [t2=.(T2 a,b,c) [t1=.(T1 e,f,g,h,16b19a4c116,48{w)
  c=.(c P t1) [g=.(t1 P t2) [t2=.(T2 h,a,b) [t1=.(T1 d,e,f,g,16b1e376c08,49{w)
  b=.(b P t1) [f=.(t1 P t2) [t2=.(T2 g,h,a) [t1=.(T1 c,d,e,f,16b2748774c,50{w)
  a=.(a P t1) [e=.(t1 P t2) [t2=.(T2 f,g,h) [t1=.(T1 b,c,d,e,16b34b0bcb5,51{w)
  h=.(h P t1) [d=.(t1 P t2) [t2=.(T2 e,f,g) [t1=.(T1 a,b,c,d,16b391c0cb3,52{w)
  g=.(g P t1) [c=.(t1 P t2) [t2=.(T2 d,e,f) [t1=.(T1 h,a,b,c,16b4ed8aa4a,53{w)
  f=.(f P t1) [b=.(t1 P t2) [t2=.(T2 c,d,e) [t1=.(T1 g,h,a,b,16b5b9cca4f,54{w)
  e=.(e P t1) [a=.(t1 P t2) [t2=.(T2 b,c,d) [t1=.(T1 f,g,h,a,16b682e6ff3,55{w)
  d=.(d P t1) [h=.(t1 P t2) [t2=.(T2 a,b,c) [t1=.(T1 e,f,g,h,16b748f82ee,56{w)
  c=.(c P t1) [g=.(t1 P t2) [t2=.(T2 h,a,b) [t1=.(T1 d,e,f,g,16b78a5636f,57{w)
  b=.(b P t1) [f=.(t1 P t2) [t2=.(T2 g,h,a) [t1=.(T1 c,d,e,f,16b84c87814,58{w)
  a=.(a P t1) [e=.(t1 P t2) [t2=.(T2 f,g,h) [t1=.(T1 b,c,d,e,16b8cc70208,59{w)
  h=.(h P t1) [d=.(t1 P t2) [t2=.(T2 e,f,g) [t1=.(T1 a,b,c,d,16b90befffa,60{w)
  g=.(g P t1) [c=.(t1 P t2) [t2=.(T2 d,e,f) [t1=.(T1 h,a,b,c,16ba4506ceb,61{w)
  f=.(f P t1) [b=.(t1 P t2) [t2=.(T2 c,d,e) [t1=.(T1 g,h,a,b,16bbef9a3f7,62{w)
  e=.(e P t1) [a=.(t1 P t2) [t2=.(T2 b,c,d) [t1=.(T1 f,g,h,a,16bc67178f2,63{w)
  a,b,c,d,e,f,g,h
)




NB. version 3 : loop unrolling via meta-programming
NB. --------------------------------------------------------------------------

NB. hex parsing/formatting routines, for the constants
NB. there is no particular reason the constants taken from k have to be in hex,
NB. but i think the generated code looks nicer when everything is the same length.
hexcode =: ,{;~ '0123456789abcdef'                NB. :: s2[256]  (where s2 :: ch[2])
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
  r =. r, '[h=.(t1 P t2)'
  r =. r, '[t2=.(T2 ', (sc a,b,c), ')'
  r =. r, '[t1=.(T1 ', (sc e,f,g,h)
  r =. r, ',16b', (u32hex ii{k), ',', (":ii), '{w)'
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
  w =. W y [ 'a b c d e f g h' =. (i. 8) { y
  do each , v3_unrolled
  a,b,c,d,e,f,g,h return.
)
