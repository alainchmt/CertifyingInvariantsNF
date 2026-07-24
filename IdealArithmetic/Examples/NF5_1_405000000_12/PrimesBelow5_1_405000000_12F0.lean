
import IdealArithmetic.Examples.NF5_1_405000000_12.RI5_1_405000000_12
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1747, 752, -3525, 5139, 5189]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-1747, 752, -3525, 5139, 5189]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1747, 752, -3525, 5139, 5189], ![31134, 20573, -8774, -38284, 10178], ![30534, -11837, 58857, -87770, -86746], ![-275805, -183480, 80320, 337213, -93883], ![-3222, 124858, -266691, 203183, 382634]]]
  hmulB := by decide  
  f := ![![![354127, 704533, 524357, 133841, 128172]], ![![384516, 765341, 570692, 145510, 139510]], ![![418530, 832379, 619831, 158162, 151510]], ![![262272, 521937, 388871, 99198, 95059]], ![![205523, 408496, 303682, 77564, 74225]]]
  g := ![![![-3468, 752, -3525, 5139, 5189], ![10478, 20573, -8774, -38284, 10178], ![58640, -11837, 58857, -87770, -86746], ![-90961, -183480, 80320, 337213, -93883], ![-192928, 124858, -266691, 203183, 382634]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-698, -1389, -1035, -264, -253]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-698, -1389, -1035, -264, -253]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-698, -1389, -1035, -264, -253], ![-1518, -3020, -2250, -574, -550], ![-1650, -3283, -2446, -624, -598], ![-1035, -2059, -1534, -391, -375], ![-111, -221, -165, -42, -40]]]
  hmulB := by decide  
  f := ![![![-52, -35, 52, 2, 14]], ![![42, 23, -37, -2, -10]], ![![-56, -32, 51, 2, 13]], ![![-3, -4, 3, 3, 1]], ![![-59, -32, 52, 2, 17]]]
  g := ![![![295, -1389, -1035, -264, -253], ![641, -3020, -2250, -574, -550], ![697, -3283, -2446, -624, -598], ![437, -2059, -1534, -391, -375], ![47, -221, -165, -42, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 5, 4, 1, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 5, 4, 1, 1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![2, 5, 4, 1, 1], ![6, 11, 8, 2, 2], ![6, 12, 9, 2, 2], ![3, 7, 6, 2, 1], ![0, 1, 0, 1, 1]]]
  hmulB := by decide  
  f := ![![![1, 4, -4, 0, -1]], ![![-3, -3, 4, 0, 1]], ![![3, 2, -3, 0, -1]], ![![-1, 2, -2, 1, 0]], ![![5, 5, -6, -1, -1]]]
  g := ![![![0, 5, 4, 1, 1], ![1, 11, 8, 2, 2], ![1, 12, 9, 2, 2], ![0, 7, 6, 2, 1], ![-1, 1, 0, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-1747, 752, -3525, 5139, 5189]] ![![-698, -1389, -1035, -264, -253]]
  ![![-724, 148, -1116, 1873, 1656]] where
 M := ![![![-724, 148, -1116, 1873, 1656]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-724, 148, -1116, 1873, 1656]] ![![-698, -1389, -1035, -264, -253]]
  ![![-283, 21, -346, 673, 525]] where
 M := ![![![-283, 21, -346, 673, 525]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-283, 21, -346, 673, 525]] ![![2, 5, 4, 1, 1]]
  ![![-497, -100, -40, 938, 265]] where
 M := ![![![-497, -100, -40, 938, 265]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-497, -100, -40, 938, 265]] ![![2, 5, 4, 1, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![980, 2766, 2480, 1364, 426]]]
 hmul := by decide  
 g := ![![![![490, 1383, 1240, 682, 213]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1268955033, 2524720590, 1881067716, 479841798, 459820282]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![1268955033, 2524720590, 1881067716, 479841798, 459820282]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1268955033, 2524720590, 1881067716, 479841798, 459820282], ![2758921692, 5489167191, 4089757584, 1043256772, 999726628], ![2999179884, 5967186352, 4445910419, 1134107844, 1086786916], ![1880899902, 3742249774, 2788199716, 711242213, 681565458], ![202027332, 401954798, 299480340, 76394478, 73206899]]]
  hmulB := by decide  
  f := ![![![17343, 10874, -3652, -22246, 3898]], ![![7796, -6369, 22080, -27660, -32260]], ![![-96780, -61112, 21291, 123460, -23060]], ![![-73078, 54310, -195612, 250821, 286110]], ![![413416, 218294, -844, -594466, -30689]]]
  g := ![![![422985011, 2524720590, 1881067716, 479841798, 459820282], ![919640564, 5489167191, 4089757584, 1043256772, 999726628], ![999726628, 5967186352, 4445910419, 1134107844, 1086786916], ![626966634, 3742249774, 2788199716, 711242213, 681565458], ![67342444, 401954798, 299480340, 76394478, 73206899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![1268955033, 2524720590, 1881067716, 479841798, 459820282]] ![![1268955033, 2524720590, 1881067716, 479841798, 459820282]]
  ![![15212844387640745733, 30267566759461270880, 22551145982775187440, 5752574642068590888, 5512547056824992684]] where
 M := ![![![15212844387640745733, 30267566759461270880, 22551145982775187440, 5752574642068590888, 5512547056824992684]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![15212844387640745733, 30267566759461270880, 22551145982775187440, 5752574642068590888, 5512547056824992684]] ![![1268955033, 2524720590, 1881067716, 479841798, 459820282]]
  ![![182378907596294429764246342173, 362862172288646154399694416574, 270354002485194427810386967476, 68964636221413368426564980750, 66087069891656623246422558006]] where
 M := ![![![182378907596294429764246342173, 362862172288646154399694416574, 270354002485194427810386967476, 68964636221413368426564980750, 66087069891656623246422558006]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![182378907596294429764246342173, 362862172288646154399694416574, 270354002485194427810386967476, 68964636221413368426564980750, 66087069891656623246422558006]] ![![1268955033, 2524720590, 1881067716, 479841798, 459820282]]
  ![![2186446208773459016832326216947217189193, 4350166537152413190601084252295647816544, 3241134029977564815610323645560055985568, 826781284048077737485198601837760058544, 792283632564619536552490303824145846168]] where
 M := ![![![2186446208773459016832326216947217189193, 4350166537152413190601084252295647816544, 3241134029977564815610323645560055985568, 826781284048077737485198601837760058544, 792283632564619536552490303824145846168]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![2186446208773459016832326216947217189193, 4350166537152413190601084252295647816544, 3241134029977564815610323645560055985568, 826781284048077737485198601837760058544, 792283632564619536552490303824145846168]] ![![1268955033, 2524720590, 1881067716, 479841798, 459820282]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![26212170512841493586498593663648992028150715871393, 52151892222888349897546377284883400815730391242830, 38856276229363016083124098530970031566523670406500, 9911852350784126327123460391697118520922953298550, 9498277884900398186039406652157228309819194060530]]]
 hmul := by decide  
 g := ![![![![8737390170947164528832864554549664009383571957131, 17383964074296116632515459094961133605243463747610, 12952092076454338694374699510323343855507890135500, 3303950783594708775707820130565706173640984432850, 3166092628300132728679802217385742769939731353510]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1198, 869, -486, -1374, 615]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![1198, 869, -486, -1374, 615]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![1198, 869, -486, -1374, 615], ![3690, -191, 4486, -8640, -6726], ![-20178, -14641, 8449, 22750, -10554], ![-33507, 1150, -39634, 77735, 59417], ![93945, 57345, -16494, -122956, 16404]]]
  hmulB := by decide  
  f := ![![![-21973045006, -43717702601, -32572300948, -8308872312, -7962182581]], ![![-27133055102, -53984089745, -40221372874, -10260075024, -9831970882]], ![![-19175892454, -38152471047, -28425870869, -7251158946, -6948602564]], ![![-24092315051, -47934215038, -35713854686, -9110251647, -8730124167]], ![![-13883482311, -27622659972, -20580532372, -5249890570, -5030837601]]]
  g := ![![![469, 869, -486, -1374, 615], ![10044, -191, 4486, -8640, -6726], ![-7570, -14641, 8449, 22750, -10554], ![-89606, 1150, -39634, 77735, 59417], ![68033, 57345, -16494, -122956, 16404]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![1198, 869, -486, -1374, 615]] ![![1198, 869, -486, -1374, 615]]
  ![![118263115, 41677684, 43523198, -202636542, -71529378]] where
 M := ![![![118263115, 41677684, 43523198, -202636542, -71529378]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![118263115, 41677684, 43523198, -202636542, -71529378]] ![![1198, 869, -486, -1374, 615]]
  ![![-512826026930, -4877297137337, 9708319982796, -6489421346272, -13880359451277]] where
 M := ![![![-512826026930, -4877297137337, 9708319982796, -6489421346272, -13880359451277]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-512826026930, -4877297137337, 9708319982796, -6489421346272, -13880359451277]] ![![1198, 869, -486, -1374, 615]]
  ![![-1301055400230575219, -945085642213979404, 546539648453144888, 1465927058174963392, -683247661129453604]] where
 M := ![![![-1301055400230575219, -945085642213979404, 546539648453144888, 1465927058174963392, -683247661129453604]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-1301055400230575219, -945085642213979404, 546539648453144888, 1465927058174963392, -683247661129453604]] ![![1198, 869, -486, -1374, 615]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-129380626878808387866710, -46447013788707303124935, -45820693877716522225350, 220350206360018515214010, 75681310891029173506115]]]
 hmul := by decide  
 g := ![![![![-25876125375761677573342, -9289402757741460624987, -9164138775543304445070, 44070041272003703042802, 15136262178205834701223]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 25, -58, -4, -16]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![89, 25, -58, -4, -16]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![1, 5, 1, 2, 1]] where
  M :=![![![89, 25, -58, -4, -16], ![-96, -25, 58, 4, 16], ![48, 9, -29, -2, -8], ![24, 8, -18, -1, -4], ![54, 11, -30, -4, -9]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0, 0, 0]], ![![0, -1, -2, 0, 0]], ![![0, -1, -1, -2, 0]], ![![0, -2, 2, -3, -4]], ![![-1, -2, -1, 0, -1]]]
  g := ![![![15, 15, -6, 4, -16], ![-16, -15, 6, -4, 16], ![8, 7, -3, 2, -8], ![4, 4, -2, 1, -4], ![9, 8, -3, 2, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [4, 1, 2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 2, 4], [2, 4, 3, 1], [1, 0, 0, 6], [0, 1]]
 g := ![![[6, 5, 0, 1], []], ![[4], [0, 5, 1]], ![[6, 3, 1, 2], [1, 0, 2, 2, 2, 1]], ![[2, 3, 2, 6, 1, 6], [4, 0, 4, 2, 0, 6]]]
 h' := ![![[4, 2, 4], [0, 0, 0, 1], [0, 1]], ![[2, 4, 3, 1], [1, 6], [4, 2, 4]], ![[1, 0, 0, 6], [4, 5, 3], [2, 4, 3, 1]], ![[0, 1], [6, 3, 4, 6], [1, 0, 0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 2, 2], []]
 b := ![[], [], [6, 5, 4, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [4, 1, 2, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2982718649, -477732939, -2305906058, 6010290620, 3536478189]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-931313834, -2594303412, -834626321, -151809394, 3536478189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, 0, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![1, 1, 0, 0, 0], ![0, 1, 2, 0, 0], ![0, 1, 1, 2, 0], ![0, 2, -2, 3, 4], ![6, 3, 0, -8, -1]]]
  hmulB := by decide  
  f := ![![![-89, -25, 58, 4, 16]], ![![1, 0, 0, 0, 0]], ![![-45, -12, 29, 2, 8]], ![![-67, -19, 44, 3, 12]], ![![-84, -23, 54, 4, 15]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 1, 2, 0, 0], ![-2, 1, 1, 2, 0], ![-5, 2, -2, 3, 4], ![7, 3, 0, -8, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![89, 25, -58, -4, -16]] ![![1, 1, 0, 0, 0]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [2, 5, 2, 10, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6, 0, 8, 8], [10, 5, 3, 8, 8], [3, 2, 5, 9, 1], [7, 8, 3, 8, 5], [0, 1]]
 g := ![![[3, 8, 9, 0, 9], [1], []], ![[2, 6, 6, 2, 7, 9, 9, 7], [4, 1, 0, 6, 9, 2, 0, 7], [10, 10, 1, 9]], ![[7, 4, 0, 8, 1, 8], [10, 7, 5, 9, 1, 8, 5, 7], [10, 3, 1, 9]], ![[9, 3, 6, 5, 1, 3, 3, 4], [3, 2, 9, 1, 1, 0, 7, 3], [6, 1, 10, 1]], ![[3, 9, 4, 1, 6, 3, 6, 9], [4, 6, 9, 10, 4, 2, 3, 1], [5, 1, 1, 3]]]
 h' := ![![[5, 6, 0, 8, 8], [9, 6, 9, 1, 3], [0, 0, 1], [0, 1]], ![[10, 5, 3, 8, 8], [7, 2, 1, 4, 4], [5, 1, 8, 3, 4], [5, 6, 0, 8, 8]], ![[3, 2, 5, 9, 1], [4, 3, 4, 10], [3, 0, 4, 6, 4], [10, 5, 3, 8, 8]], ![[7, 8, 3, 8, 5], [10, 7, 9, 8, 2], [8, 2, 8, 4, 6], [3, 2, 5, 9, 1]], ![[0, 1], [2, 4, 10, 10, 2], [6, 8, 1, 9, 8], [7, 8, 3, 8, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 0, 0, 5], [], [], []]
 b := ![[], [6, 3, 5, 8, 9], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [2, 5, 2, 10, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14534418113353952, 10305466942656765, -5574160733666448, -16772056806460934, 6870648548498196]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1321310737577632, 936860631150615, -506741884878768, -1524732436950994, 624604413499836]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 161051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1351, 2727, 2028, 518, 496]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![1351, 2727, 2028, 518, 496]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![12, 5, 9, 1, 0], ![5, 10, 9, 0, 1]] where
  M :=![![![1351, 2727, 2028, 518, 496], ![2976, 5903, 4418, 1124, 1080], ![3240, 6441, 4779, 1222, 1168], ![2016, 4032, 3010, 767, 736], ![228, 445, 308, 82, 75]]]
  hmulB := by decide  
  f := ![![![-5, -5, 6, 2, -8]], ![![-48, -19, -14, 80, 24]], ![![72, 85, -99, -30, 136]], ![![60, 60, -59, -43, 80]], ![![-25, 11, -51, 74, 75]]]
  g := ![![![-565, -371, -546, 518, 496], ![-1224, -809, -1186, 1124, 1080], ![-1328, -873, -1287, 1222, 1168], ![-836, -551, -809, 767, 736], ![-87, -55, -85, 82, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [8, 0, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10, 11], [12, 2, 2], [0, 1]]
 g := ![![[9, 2, 1], [8, 12], [1]], ![[1, 0, 9, 2], [5, 9], [3, 2, 2, 5]], ![[2, 4, 3, 7], [12, 4], [7, 7, 12, 8]]]
 h' := ![![[6, 10, 11], [0, 8, 12], [5, 0, 5], [0, 1]], ![[12, 2, 2], [8, 5, 8], [10, 11, 10], [6, 10, 11]], ![[0, 1], [7, 0, 6], [8, 2, 11], [12, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 12], []]
 b := ![[], [5, 9, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [8, 0, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1477691, 536682, 507373, -2506591, -843079]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2751706, 1653879, 2358031, -2506591, -843079]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 5, -6, -2, 8]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![5, 5, -6, -2, 8]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![12, 4, 1, 0, 0], ![4, 10, 0, 1, 0], ![9, 11, 0, 0, 1]] where
  M :=![![![5, 5, -6, -2, 8], ![48, 19, 14, -80, -24], ![-72, -85, 99, 30, -136], ![-432, -170, -122, 713, 208], ![468, 407, -338, -422, 449]]]
  hmulB := by decide  
  f := ![![![-1351, -2727, -2028, -518, -496]], ![![-2976, -5903, -4418, -1124, -1080]], ![![-2412, -4829, -3599, -918, -880]], ![![-2860, -5690, -4254, -1083, -1040]], ![![-3471, -6917, -5166, -1316, -1263]]]
  g := ![![![1, -3, -6, -2, 8], ![32, 79, 14, -80, -24], ![-12, 55, 99, 30, -136], ![-284, -700, -122, 713, 208], ![167, 80, -338, -422, 449]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12], [0, 1]]
 g := ![![[10, 12], [1], [7, 1]], ![[3, 1], [1], [1, 12]]]
 h' := ![![[7, 12], [3, 5], [1, 12], [0, 1]], ![[0, 1], [12, 8], [7, 1], [7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [4, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [11, 6, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19431, 11360, -41413, 61416, 63198]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25917, -87102, -41413, 61416, 63198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![1351, 2727, 2028, 518, 496]] ![![5, 5, -6, -2, 8]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-277, -739, 1250, -532, -1772]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-277, -739, 1250, -532, -1772]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![2, 10, 13, 1, 0], ![3, 15, 7, 0, 1]] where
  M :=![![![-277, -739, 1250, -532, -1772], ![-10632, -5407, -414, 15612, 1416], ![4248, 12213, -21019, 9534, 29808], ![94740, 48564, 2886, -138523, -11448], ![-57102, -68913, 81798, 21300, -112879]]]
  hmulB := by decide  
  f := ![![![7566403, 15054221, 11216312, 2861168, 2741788]], ![![16450728, 32730415, 24386106, 6220656, 5961096]], ![![17883288, 35580717, 26509759, 6762378, 6480216]], ![![24902242, 49545643, 36914461, 9416515, 9023608]], ![![23285163, 46328274, 34517327, 8805030, 8437637]]]
  g := ![![![359, 1833, 1210, -532, -1772], ![-2712, -10751, -12546, 15612, 1416], ![-6132, -31191, -20801, 9534, 29808], ![23890, 94442, 110813, -138523, -11448], ![14055, 83016, 35003, 21300, -112879]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [14, 1, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 9, 1], [8, 7, 16], [0, 1]]
 g := ![![[10, 12, 8], [3, 4], [4, 1], []], ![[0, 9, 7, 1], [11, 4], [10, 15], [5, 1]], ![[3, 10, 6, 1], [], [7, 13], [7, 1]]]
 h' := ![![[13, 9, 1], [0, 2, 12], [12, 16, 15], [0, 0, 1], [0, 1]], ![[8, 7, 16], [7, 14, 1], [5, 3, 2], [14, 11, 7], [13, 9, 1]], ![[0, 1], [16, 1, 4], [4, 15], [0, 6, 9], [8, 7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 4], []]
 b := ![[], [14, 16, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [14, 1, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11703491, -14732187, 18046461, 3411199, -24971930]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3317053, 19160869, 8735552, 3411199, -24971930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7566403, 15054221, 11216312, 2861168, 2741788]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![7566403, 15054221, 11216312, 2861168, 2741788]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![11, 4, 1, 0, 0], ![7, 7, 0, 1, 0], ![6, 8, 0, 0, 1]] where
  M :=![![![7566403, 15054221, 11216312, 2861168, 2741788], ![16450728, 32730415, 24386106, 6220656, 5961096], ![17883288, 35580717, 26509759, 6762378, 6480216], ![11215284, 22314018, 16625286, 4240945, 4063992], ![1204626, 2396751, 1785720, 455520, 436513]]]
  hmulB := by decide  
  f := ![![![-277, -739, 1250, -532, -1772]], ![![-10632, -5407, -414, 15612, 1416]], ![![-2431, -1032, -525, 3890, 940]], ![![1081, 326, 514, -1939, -820]], ![![-8460, -6859, 5058, 8412, -6599]]]
  g := ![![![-8958349, -4221971, 11216312, 2861168, 2741788], ![-19476918, -9179257, 24386106, 6220656, 5961096], ![-21173059, -9978629, 26509759, 6762378, 6480216], ![-13278437, -6257981, 16625286, 4240945, 4063992], ![-1426236, -672169, 1785720, 455520, 436513]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16], [0, 1]]
 g := ![![[2, 2], [1], [9], [1]], ![[13, 15], [1], [9], [1]]]
 h' := ![![[14, 16], [5, 11], [10, 16], [7, 14], [0, 1]], ![[0, 1], [6, 6], [13, 1], [16, 3], [14, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [16, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [10, 3, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21130, 10760, 1478, -31414, -3140]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14330, 14698, 1478, -31414, -3140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-277, -739, 1250, -532, -1772]] ![![7566403, 15054221, 11216312, 2861168, 2741788]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2081515, -1109391, 25952, 2976930, 123398]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-2081515, -1109391, 25952, 2976930, 123398]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![4, 1, 1, 1, 0], ![15, 15, 18, 0, 1]] where
  M :=![![![-2081515, -1109391, 25952, 2976930, 123398], ![740388, 4268491, -8172642, 5018580, 11660924], ![34982772, 18793839, -750089, -49797758, -1623764], ![-5241486, -37251308, 72677918, -46562081, -103802214], ![-135961386, -58385265, -27972296, 216535218, 50597789]]]
  hmulB := by decide  
  f := ![![![-34183250341, -68011199125, -50672406730, -12926030678, -12386688746]], ![![-74320132476, -147867784665, -110170336894, -28103364848, -26930745220]], ![![-80792235660, -160744717363, -119764419817, -30550720862, -29275984476]], ![![-18027013510, -35866654290, -26722800615, -6816722567, -6532293122]], ![![-162487011531, -323285135353, -240866744464, -61442727956, -58879015021]]]
  g := ![![![-833695, -312489, -272218, 2976930, 123398], ![-10223568, -9245471, -11741466, 5018580, 11660924], ![13606856, 4892003, 4119759, -49797758, -1623764], ![91475792, 82439157, 104614729, -46562081, -103802214], ![-92687847, -54415122, -60803564, 216535218, 50597789]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [18, 5, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 4, 5], [2, 14, 14], [0, 1]]
 g := ![![[13, 1, 9], [7, 16, 7], [15, 1], []], ![[7, 17], [0, 14, 9, 17], [18, 6], [16, 6]], ![[4, 18, 6, 12], [3, 5, 16, 15], [0, 16], [7, 6]]]
 h' := ![![[13, 4, 5], [7, 16, 16], [15, 2, 11], [0, 0, 1], [0, 1]], ![[2, 14, 14], [2, 12], [5, 15, 12], [14, 11, 14], [13, 4, 5]], ![[0, 1], [6, 10, 3], [7, 2, 15], [11, 8, 4], [2, 14, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [15, 4, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [18, 5, 4, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2784407, -6365301, 10315220, -3667050, -14578205]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12134572, 11367096, 14546840, -3667050, -14578205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![215039700298, 427844282033, 318769557484, 81314966186, 77922079315]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![215039700298, 427844282033, 318769557484, 81314966186, 77922079315]] 
 ![![19, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![215039700298, 427844282033, 318769557484, 81314966186, 77922079315], ![467532475890, 930205428099, 693058631694, 176792412820, 169415706114], ![508247118342, 1011211525783, 753413015279, 192188220058, 184169119526], ![318741120633, 634169252108, 472493989878, 120528550823, 115499467533], ![34235962209, 68116076477, 50750547496, 12945963492, 12405789996]]]
  hmulB := by decide  
  f := ![![![-8486, -4947, 358, 12456, -423]], ![![-3260, -1006, -1700, 6116, 2511]], ![![6214, 3503, -635, -8350, 298]], ![![-3685, -10019, 16640, -6783, -23910]], ![![-35171, -16712, -4104, 53886, 8375]]]
  g := ![![![-289203562480, 427844282033, 318769557484, 81314966186, 77922079315], ![-628777185863, 930205428099, 693058631694, 176792412820, 169415706114], ![-683533677925, 1011211525783, 753413015279, 192188220058, 184169119526], ![-428669996601, 634169252108, 472493989878, 120528550823, 115499467533], ![-46043415342, 68116076477, 50750547496, 12945963492, 12405789996]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3520, -2348, 3502, 134, 937]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-3520, -2348, 3502, 134, 937]] 
 ![![19, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![-3520, -2348, 3502, 134, 937], ![5622, 3061, -4964, -224, -1338], ![-4014, -1902, 3285, 164, 890], ![-141, -396, 416, 1, 107], ![-4587, -2134, 3718, 188, 1008]]]
  hmulB := by decide  
  f := ![![![-4, -2, -58, 12, 51]], ![![14, 5, -32, -20, 24]], ![![-10, -24, 11, -12, -31]], ![![-161, -84, -58, 239, 64]], ![![91, 112, -178, -26, 224]]]
  g := ![![![-1050, -2348, 3502, 134, 937], ![1700, 3061, -4964, -224, -1338], ![-1223, -1902, 3285, 164, 890], ![-32, -396, 416, 1, 107], ![-1399, -2134, 3718, 188, 1008]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-2081515, -1109391, 25952, 2976930, 123398]] ![![215039700298, 427844282033, 318769557484, 81314966186, 77922079315]]
  ![![-4, -2, -58, 12, 51]] where
 M := ![![![-4, -2, -58, 12, 51]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-4, -2, -58, 12, 51]] ![![-3520, -2348, 3502, 134, 937]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77674831, 154542312, 115143258, 29371908, 28146358]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![77674831, 154542312, 115143258, 29371908, 28146358]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![8, 10, 21, 5, 1]] where
  M :=![![![77674831, 154542312, 115143258, 29371908, 28146358], ![168878148, 336000979, 250340808, 63859468, 61194916], ![183584748, 365261320, 272141511, 69420612, 66524020], ![115132986, 229069282, 170670304, 43536309, 41719746], ![12366426, 24604316, 18331686, 4676232, 4481115]]]
  hmulB := by decide  
  f := ![![![293, 168, -266, -12, -74]], ![![-444, -219, 360, 36, 100]], ![![300, 144, -255, -4, -28]], ![![138, 86, -32, -165, -30]], ![![224, 116, -183, -27, -23]]]
  g := ![![![-6412871, -5518316, -20692620, -4841734, 28146358], ![-13942660, -11997747, -44989236, -10526744, 61194916], ![-15156844, -13042560, -48907083, -11443456, 66524020], ![-9505434, -8179486, -30671494, -7176627, 41719746], ![-1020978, -878558, -3294423, -770841, 4481115]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [7, 14, 19, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 17, 10, 5], [22, 11, 20, 13], [19, 17, 16, 5], [0, 1]]
 g := ![![[2, 20, 2, 6], [10, 8, 1, 9], [4, 1], []], ![[20, 11, 15, 18, 16, 19], [8, 1, 0, 18, 5, 15], [16, 13, 11, 13, 15, 19], [20, 16, 2]], ![[18, 1, 15, 0, 0, 6], [1, 22, 10, 9, 19, 1], [11, 16, 3, 13], [5, 0, 8]], ![[9, 2, 15, 11, 20, 15], [9, 20, 14, 19, 4, 14], [2, 12, 18, 13, 1, 19], [2, 7, 2]]]
 h' := ![![[9, 17, 10, 5], [22, 13, 22, 11], [18, 6, 2, 20], [0, 0, 1], [0, 1]], ![[22, 11, 20, 13], [15, 5, 7, 17], [6, 4, 16, 16], [10, 6, 12, 17], [9, 17, 10, 5]], ![[19, 17, 16, 5], [4, 22, 21, 2], [9, 7, 12, 19], [12, 0, 22], [22, 11, 20, 13]], ![[0, 1], [17, 6, 19, 16], [16, 6, 16, 14], [2, 17, 11, 6], [19, 17, 16, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 19, 4], []]
 b := ![[], [], [19, 18, 8, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [7, 14, 19, 19, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42110727, 3461781, 39473979, -90005702, -59848472]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22647761, 26171587, 56360517, 9097246, -59848472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-293, -168, 266, 12, 74]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-293, -168, 266, 12, 74]] 
 ![![23, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-293, -168, 266, 12, 74], ![444, 219, -360, -36, -100], ![-300, -144, 255, 4, 28], ![-138, -86, 32, 165, 30], ![-258, -60, 166, -24, 199]]]
  hmulB := by decide  
  f := ![![![-77674831, -154542312, -115143258, -29371908, -28146358]], ![![-24228361, -48204893, -35915526, -9161696, -8779422]], ![![-82279610, -163704008, -121969269, -31113156, -29814952]], ![![-5005782, -9959534, -7420448, -1892883, -1813902]], ![![-68081002, -135454372, -100921602, -25744104, -24669925]]]
  g := ![![![-295, -168, 266, 12, 74], ![403, 219, -360, -36, -100], ![-250, -144, 255, 4, 28], ![-44, -86, 32, 165, 30], ![-330, -60, 166, -24, 199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![77674831, 154542312, 115143258, 29371908, 28146358]] ![![-293, -168, 266, 12, 74]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB1253I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1253I0 : PrimesBelowBoundCertificateInterval O 1 23 1253 where
  m := 9
  g := ![5, 5, 5, 2, 1, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1253I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![161051]
    · exact ![2197, 169]
    · exact ![4913, 289]
    · exact ![6859, 19, 19]
    · exact ![279841, 23]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N1, I13N1, I17N1, I19N1, I19N2, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [I17N1], [I19N1, I19N2], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
