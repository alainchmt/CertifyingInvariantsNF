
import IdealArithmetic.Examples.NF3_1_975819_1.RI3_1_975819_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49665060825818917005169495898255282977786837, -8655565498827064275514880693642085078280643, 2810221365316070714332645007241968132408512]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![49665060825818917005169495898255282977786837, -8655565498827064275514880693642085078280643, 2810221365316070714332645007241968132408512]] 
 ![![197, 0, 0], ![0, 197, 0], ![125, 143, 1]] where
  M :=![![![49665060825818917005169495898255282977786837, -8655565498827064275514880693642085078280643, 2810221365316070714332645007241968132408512], ![-814514393135902802891433160756338397036358266, 141952563075491546313112889793407869985157519, -46088048859451392091907048475452393523811727], ![3017303248834014481274293176491256020621249272, -525851885930432244605367562537253182924315381, 170729480937288809853990176881576093352407960]]]
  hmulB := by decide  
  f := ![![![-10440095776555454136151, 1846632774969058325864, 670339306001277279689]], ![![-202113700126316191439672, 19396402707432476423448, 8562824568844014349631]], ![![-155559794030209550700701, 15388937201805503128201, 6714736904991778125299]]]
  g := ![![![-1531028476338527524296503198005029104432879, -2083843760096574499619711252432708264023847, 2810221365316070714332645007241968132408512], ![25109094996423965525872831972970613164670597, 34175347969426602108912796049660406821777840, -46088048859451392091907048475452393523811727], ![-93014628773233942895809537734546982986953024, -126599835837374274384395750541130124529536313, 170729480937288809853990176881576093352407960]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [92, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 196], [0, 1]]
 g := ![![[104, 15], [26], [168, 155], [61], [70], [105], [85, 1]], ![[0, 182], [26], [144, 42], [61], [70], [105], [170, 196]]]
 h' := ![![[85, 196], [192, 58], [107, 82], [72, 67], [103, 88], [47, 55], [60, 41], [0, 1]], ![[0, 1], [0, 139], [182, 115], [54, 130], [97, 109], [191, 142], [196, 156], [85, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166]]
 b := ![[], [117, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [92, 112, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4528, -835, 435]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-299, -320, 435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10440095776555454136151, 1846632774969058325864, 670339306001277279689]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-10440095776555454136151, 1846632774969058325864, 670339306001277279689]] 
 ![![197, 0, 0], ![74, 1, 0], ![175, 0, 1]] where
  M :=![![![-10440095776555454136151, 1846632774969058325864, 670339306001277279689], ![-202113700126316191439672, 19396402707432476423448, 8562824568844014349631], ![-438008333818634345146126, 27105944721707696969533, 14526843688526578725545]]]
  hmulB := by decide  
  f := ![![![49665060825818917005169495898255282977786837, -8655565498827064275514880693642085078280643, 2810221365316070714332645007241968132408512]], ![![14521320345049223631934566171139860625989176, -2530757785978229492766437977340641755368579, 821666660781410359232023766804331209514813]], ![![59434969001788451559284035323278835237228151, -10358253036675982197058231898094507977783898, 3363036649074117689655853061669647291999480]]]
  g := ![![![-1342133500885732457846, 1846632774969058325864, 670339306001277279689], ![-15918486294538182527717, 19396402707432476423448, 8562824568844014349631], ![-25309877607701295420619, 27105944721707696969533, 14526843688526578725545]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![49665060825818917005169495898255282977786837, -8655565498827064275514880693642085078280643, 2810221365316070714332645007241968132408512]] ![![-10440095776555454136151, 1846632774969058325864, 670339306001277279689]]
  ![![197, 0, 0]] where
 M := ![![![197, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2056536225128172108802767147478151297, 358410594919752547083529552025815222, -116365951079178124435940480849686350]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-2056536225128172108802767147478151297, 358410594919752547083529552025815222, -116365951079178124435940480849686350]] 
 ![![199, 0, 0], ![0, 199, 0], ![95, 136, 1]] where
  M :=![![![-2056536225128172108802767147478151297, 358410594919752547083529552025815222, -116365951079178124435940480849686350], ![33727500329597219738871323227455529156, -5877987127376613867637386796564288503, 1908418925677940859853588240978762460], ![-124940820171073610095347105297290494412, 21774531924175283673465664745935779108, -7069584863215049633323915933491420519]]]
  hmulB := by decide  
  f := ![![![-3322652865780137223, -94043992055831982, 29304171398346070]], ![![-8485946749798772756, -2367878165356304457, -499524131677505980]], ![![-7221891873400441211, -1691440728179035570, -337727777100946729]]]
  g := ![![![45217231795948491018148635845437447, 81327537395416972212921783656196778, -116365951079178124435940480849686350], ![-741569334722649055011153566158426656, -1333783723716465179938318530500884337, 1908418925677940859853588240978762460], ![2747084129820884950102637730574846507, 4940894840811165999022704681913411908, -7069584863215049633323915933491420519]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [42, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 198], [0, 1]]
 g := ![![[76, 86], [174, 106], [162, 64], [40], [94], [86], [191, 1]], ![[184, 113], [122, 93], [48, 135], [40], [94], [86], [183, 198]]]
 h' := ![![[191, 198], [55, 177], [161, 107], [67, 8], [126, 55], [33, 166], [137, 22], [0, 1]], ![[0, 1], [32, 22], [101, 92], [3, 191], [84, 144], [98, 33], [160, 177], [191, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [46, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [42, 8, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9139, -7772, 5708]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2679, -3940, 5708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3322652865780137223, 94043992055831982, -29304171398346070]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![3322652865780137223, 94043992055831982, -29304171398346070]] 
 ![![199, 0, 0], ![117, 1, 0], ![1, 0, 1]] where
  M :=![![![3322652865780137223, 94043992055831982, -29304171398346070], ![8485946749798772756, 2367878165356304457, 499524131677505980], ![-32584297415058330012, 5631095173866633988, 2056442017790462441]]]
  hmulB := by decide  
  f := ![![![2056536225128172108802767147478151297, -358410594919752547083529552025815222, 116365951079178124435940480849686350]], ![![1039634361861301090407298658429588807, -181186193357961980608721461258573329, 58826117339627636679153005117761510]], ![![638177670332672272382662675601852491, -111220816678869528746478363306339670, 36110305599468481194773147810759331]]]
  g := ![![![-38448191122381199, 94043992055831982, -29304171398346070], ![-1352036797630986707, 2367878165356304457, 499524131677505980], ![-3484818466207261151, 5631095173866633988, 2056442017790462441]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-2056536225128172108802767147478151297, 358410594919752547083529552025815222, -116365951079178124435940480849686350]] ![![3322652865780137223, 94043992055831982, -29304171398346070]]
  ![![199, 0, 0]] where
 M := ![![![-199, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 0, 0]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![211, 0, 0]] 
 ![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]] where
  M :=![![![211, 0, 0], ![0, 211, 0], ![0, 0, 211]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [11, 50, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 36, 51], [71, 174, 160], [0, 1]]
 g := ![![[149, 19, 199], [81, 19, 44], [10, 183], [198, 71], [74, 140, 44], [148, 52], [1]], ![[196, 117, 149, 46], [144, 91, 0, 5], [24, 119], [65, 79], [113, 133, 77, 46], [190, 96], [164, 60, 136, 143]], ![[44, 158, 209, 197], [163, 22, 177, 160], [4, 169], [110, 70], [89, 55, 194, 210], [180, 209], [60, 165, 79, 68]]]
 h' := ![![[49, 36, 51], [164, 62, 153], [34, 200, 172], [199, 54, 82], [30, 91, 156], [181, 91, 39], [200, 161, 120], [0, 1]], ![[71, 174, 160], [86, 132, 33], [70, 40, 38], [40, 140, 142], [79, 55, 135], [56, 97, 33], [6, 202, 184], [49, 36, 51]], ![[0, 1], [127, 17, 25], [128, 182, 1], [159, 17, 198], [37, 65, 131], [70, 23, 139], [28, 59, 118], [71, 174, 160]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 168], []]
 b := ![[], [102, 104, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [11, 50, 91, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26849806337, 18549087226, -9836552452]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-127250267, 87910366, -46618732]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def PBC211 : ContainsPrimesAboveP 211 ![I211N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![211, 0, 0]]) timesTableT_eq_Table B_one_repr 211 (by decide) 𝕀

instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 0, 0]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![223, 0, 0]] 
 ![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]] where
  M :=![![![223, 0, 0], ![0, 223, 0], ![0, 0, 223]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [187, 193, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 49, 183], [142, 173, 40], [0, 1]]
 g := ![![[32, 102, 4], [87, 47, 58], [190, 118, 110], [21, 79, 7], [63, 67, 171], [38, 152], [1]], ![[59, 147, 173, 55], [11, 76, 40, 43], [214, 168, 25, 130], [110, 46, 4, 175], [123, 134, 16, 203], [38, 68], [63, 8, 114, 1]], ![[109, 160, 45, 23], [63, 121, 194, 71], [18, 201, 2, 214], [197, 66, 75, 51], [214, 30, 140, 206], [194, 82], [114, 53, 215, 222]]]
 h' := ![![[37, 49, 183], [10, 42, 221], [150, 123, 113], [87, 12, 188], [38, 209, 26], [211, 75, 174], [36, 30, 179], [0, 1]], ![[142, 173, 40], [96, 118, 204], [4, 123, 134], [40, 88, 155], [95, 4, 152], [24, 76, 119], [70, 45, 108], [37, 49, 183]], ![[0, 1], [105, 63, 21], [108, 200, 199], [214, 123, 103], [88, 10, 45], [90, 72, 153], [58, 148, 159], [142, 173, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [204, 168], []]
 b := ![[], [84, 21, 138], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [187, 193, 44, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30206465, 6761583, -2408400]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-135455, 30321, -10800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def PBC223 : ContainsPrimesAboveP 223 ![I223N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![223, 0, 0]]) timesTableT_eq_Table B_one_repr 223 (by decide) 𝕀

instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-22, 66, 1]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-22, 66, 1]] 
 ![![227, 0, 0], ![0, 227, 0], ![205, 66, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-22, 66, 1], ![-428, 149, 329], ![-19374, 2507, -48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-205, -66, 227]], ![![-1, 0, 1], ![-299, -95, 329], ![-42, 25, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [218, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [126, 226], [0, 1]]
 g := ![![[14, 23], [82, 196], [188], [160], [1], [209, 25], [126, 1]], ![[188, 204], [35, 31], [188], [160], [1], [181, 202], [25, 226]]]
 h' := ![![[126, 226], [57, 134], [110, 14], [190, 142], [148, 29], [65, 1], [226, 222], [0, 1]], ![[0, 1], [143, 93], [58, 213], [149, 85], [170, 198], [191, 226], [50, 5], [126, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [47, 165]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [218, 101, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4424, -802, 490]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-462, -146, 490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 0, 0], ![-102, 1, 0]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![227, 0, 0], ![-102, 1, 0]] 
 ![![227, 0, 0], ![125, 1, 0], ![48, 0, 1]] where
  M :=![![![227, 0, 0], ![0, 227, 0], ![0, 0, 227]], ![![-102, 1, 0], ![-2, -100, 5], ![-296, 39, -103]]]
  hmulB := by decide  
  f := ![![![-47651, -2607044, 130350], ![9988, -5917890, 0]], ![![-26159, -1435525, 71775], ![5676, -3258585, 0]], ![![-9996, -551270, 27563], ![2290, -1251360, 0]]]
  g := ![![![1, 0, 0], ![-125, 227, 0], ![-48, 0, 227]], ![![-1, 1, 0], ![54, -100, 5], ![-1, 39, -103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![227, 0, 0], ![-22, 66, 1]] ![![227, 0, 0], ![-102, 1, 0]]
  ![![227, 0, 0]] where
 M := ![![![51529, 0, 0], ![-23154, 227, 0]], ![![-4994, 14982, 227], ![1816, -6583, 227]]]
 hmul := by decide  
 g := ![![![![227, 0, 0]], ![![-102, 1, 0]]], ![![![-22, 66, 1]], ![![8, -29, 1]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1683708048277692906867, -195415176378039364922, -80465871808396671826]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![1683708048277692906867, -195415176378039364922, -80465871808396671826]] 
 ![![229, 0, 0], ![0, 229, 0], ![157, 207, 1]] where
  M :=![![![1683708048277692906867, -195415176378039364922, -80465871808396671826], ![24208728408041493590340, -1845291305005856024191, -896610010081800152784], ![44807420974939391181100, -2229978467580958219616, -1339511647680134601251]]]
  hmulB := by decide  
  f := ![![![-2062743144621221873704877861992805978393, 359492329187761527553156755209052222614, -116717160107862076173920734741698629258]], ![![33829294733551651492374223973124689815140, -5895727730452319789381473006500948074227, 1914178806046669713939704510786959742328]], ![![28617883959662047843903445325475570381191, -4987489493255904706977700869419337150971, 1619299112823593093353704866251459294747]]]
  g := ![![![62518995293432185081, 71882184663581099140, -80465871808396671826], ![720421397340105316932, 802414763239854915293, -896610010081800152784], ![1114020740876508836583, 1201087041931034516329, -1339511647680134601251]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [98, 153, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 228], [0, 1]]
 g := ![![[74, 132], [178], [142, 58], [135], [171], [86, 148], [76, 1]], ![[30, 97], [178], [199, 171], [135], [171], [113, 81], [152, 228]]]
 h' := ![![[76, 228], [21, 210], [53, 112], [27, 150], [152, 140], [45, 20], [109, 182], [0, 1]], ![[0, 1], [180, 19], [92, 117], [206, 79], [29, 89], [191, 209], [201, 47], [76, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [122, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [98, 153, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99970, 14503, 6013]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4559, -5372, 6013]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2062743144621221873704877861992805978393, -359492329187761527553156755209052222614, 116717160107862076173920734741698629258]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![2062743144621221873704877861992805978393, -359492329187761527553156755209052222614, 116717160107862076173920734741698629258]] 
 ![![229, 0, 0], ![111, 1, 0], ![10, 0, 1]] where
  M :=![![![2062743144621221873704877861992805978393, -359492329187761527553156755209052222614, 116717160107862076173920734741698629258], ![-33829294733551651492374223973124689815140, 5895727730452319789381473006500948074227, -1914178806046669713939704510786959742328], ![125317909377051068495909558570034635833540, -21840250565549458678225802680846844842232, 7090921878123466448214864006869803371327]]]
  hmulB := by decide  
  f := ![![![-1683708048277692906867, 195415176378039364922, 80465871808396671826]], ![![-921835466230853302413, 102778933986760810177, 42918435724077863430]], ![![-269189962697451180130, 18271311053979702484, 9363189370148914059]]]
  g := ![![![178162533115214544412078909793801818323, -359492329187761527553156755209052222614, 116717160107862076173920734741698629258], ![-2921892073158482318665155819156595321533, 5895727730452319789381473006500948074227, -1914178806046669713939704510786959742328], ![10823914861885617106099672559280944889118, -21840250565549458678225802680846844842232, 7090921878123466448214864006869803371327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![1683708048277692906867, -195415176378039364922, -80465871808396671826]] ![![2062743144621221873704877861992805978393, -359492329187761527553156755209052222614, 116717160107862076173920734741698629258]]
  ![![229, 0, 0]] where
 M := ![![![-229, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![48, 1, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![48, 1, 0]] 
 ![![233, 0, 0], ![48, 1, 0], ![172, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![48, 1, 0], ![-2, 50, 5], ![-296, 39, 47]]]
  hmulB := by decide  
  f := ![![![-10415, 265204, 26520], ![-932, -1235832, 0]], ![![-2184, 54600, 5460], ![1, -254436, 0]], ![![-7684, 195773, 19577], ![-709, -912288, 0]]]
  g := ![![![1, 0, 0], ![-48, 233, 0], ![-172, 0, 233]], ![![0, 1, 0], ![-14, 50, 5], ![-44, 39, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N0 : Nat.card (O ⧸ I233N0) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N0)

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := prime_ideal_of_norm_prime hp233.out _ NI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![88, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![88, 1, 0]] 
 ![![233, 0, 0], ![88, 1, 0], ![0, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![88, 1, 0], ![-2, 90, 5], ![-296, 39, 87]]]
  hmulB := by decide  
  f := ![![![-87, -1, 0], ![233, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-80, -55, -3], ![215, 140, 0]]]
  g := ![![![1, 0, 0], ![-88, 233, 0], ![0, 0, 233]], ![![0, 1, 0], ![-34, 90, 5], ![-16, 39, 87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40162236487659538849529442406022666244691113, -6999425002568441133068707147865647366549995, 2272518611269343946515013582488664032560822]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![40162236487659538849529442406022666244691113, -6999425002568441133068707147865647366549995, 2272518611269343946515013582488664032560822]] 
 ![![233, 0, 0], ![96, 1, 0], ![215, 0, 1]] where
  M :=![![![40162236487659538849529442406022666244691113, -6999425002568441133068707147865647366549995, 2272518611269343946515013582488664032560822], ![-658666658930588925902306606120913258904903322, 114791612322027070497477557827349268781463181, -37269643624111549611858549321816900865310797], ![2439977815785892294723769516131395193773651684, -425236322055215248606185488793500737477024879, 138062405941001737843198692853434874913673988]]]
  hmulB := by decide  
  f := ![![![325006939830291823117265, -2473218206730441660478, -6017280917736222298767]], ![![141573939106315011600916, -652542490218901842324, -2506471151152761058735]], ![![298857361133183196091473, -965835206099593509631, -5179941957020233568274]]]
  g := ![![![959294142967042657181963126034601057651991, -6999425002568441133068707147865647366549995, 2272518611269343946515013582488664032560822], ![-15732566792537358485453064606677293458727671, 114791612322027070497477557827349268781463181, -37269643624111549611858549321816900865310797], ![58280031999017950749484366853300291352481256, -425236322055215248606185488793500737477024879, 138062405941001737843198692853434874913673988]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![48, 1, 0]] ![![233, 0, 0], ![88, 1, 0]]
  ![![325006939830291823117265, -2473218206730441660478, -6017280917736222298767]] where
 M := ![![![54289, 0, 0], ![20504, 233, 0]], ![![11184, 233, 0], ![4222, 138, 5]]]
 hmul := by decide  
 g := ![![![![9357801101624672551940360080603281235013029329, -1630866025598446784005008765452695836406148835, 529496836425757139537998164719858719586671526]], ![![2875610151983450492856284325609081370627914622, -501157787903995749212568671184827699474936379, 162711994167590717681462645937185534000041539]]], ![![![1269120692477068938875106629368174720840270102, -221180787801258103889820385270201804812936579, 71811249716816959820862102637638972697608659]], ![![389995075525350912969158119202569283798615790, -67967860389185832524442515202068960416812379, 22067273761187918390411592288084041204408886]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![325006939830291823117265, -2473218206730441660478, -6017280917736222298767]] ![![40162236487659538849529442406022666244691113, -6999425002568441133068707147865647366549995, 2272518611269343946515013582488664032560822]]
  ![![233, 0, 0]] where
 M := ![![![233, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0]] 
 ![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]] where
  M :=![![![239, 0, 0], ![0, 239, 0], ![0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [88, 127, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 164, 178], [234, 74, 61], [0, 1]]
 g := ![![[189, 199, 163], [194, 97, 27], [80, 234, 60], [112, 197, 49], [86, 12], [176, 161, 45], [1]], ![[68, 167, 164, 224], [46, 190, 15, 154], [169, 209, 67, 175], [123, 146, 28, 37], [71, 200], [235, 90, 126, 221], [36, 120, 195, 69]], ![[222, 221, 137, 153], [142, 203, 157, 192], [141, 192, 165, 24], [65, 196, 83, 68], [66, 49], [143, 231, 104, 48], [203, 98, 114, 170]]]
 h' := ![![[98, 164, 178], [136, 217, 101], [130, 221, 160], [182, 151, 120], [138, 30, 7], [47, 143, 212], [151, 112, 93], [0, 1]], ![[234, 74, 61], [219, 86, 212], [221, 136, 32], [179, 73, 147], [209, 60, 122], [237, 202, 34], [188, 63, 50], [98, 164, 178]], ![[0, 1], [81, 175, 165], [58, 121, 47], [142, 15, 211], [199, 149, 110], [157, 133, 232], [175, 64, 96], [234, 74, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 23], []]
 b := ![[], [151, 216, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [88, 127, 146, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10353480, 1842451, -482302]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43320, 7709, -2018]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0]] 
 ![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]] where
  M :=![![![241, 0, 0], ![0, 241, 0], ![0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [220, 189, 181, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 171, 43], [237, 69, 198], [0, 1]]
 g := ![![[26, 171, 81], [107, 121], [126, 216], [32, 201], [119, 144, 25], [217, 38, 226], [1]], ![[183, 166, 141, 189], [231, 18], [31, 83], [211, 158], [229, 186, 44, 109], [142, 214, 224, 222], [38, 155, 27, 218]], ![[46, 45, 82, 70], [175, 145], [105, 10], [239, 123], [203, 183, 162, 7], [72, 96, 139, 137], [109, 183, 210, 23]]]
 h' := ![![[64, 171, 43], [17, 140, 232], [136, 124, 11], [158, 188, 162], [89, 56, 125], [219, 232, 236], [21, 52, 60], [0, 1]], ![[237, 69, 198], [151, 201, 97], [222, 10, 66], [189, 104, 223], [133, 117, 188], [122, 54, 232], [11, 139, 110], [64, 171, 43]], ![[0, 1], [11, 141, 153], [34, 107, 164], [38, 190, 97], [70, 68, 169], [54, 196, 14], [56, 50, 71], [237, 69, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175, 175], []]
 b := ![[], [193, 120, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [220, 189, 181, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6460246, -3549930, 2082240]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26806, -14730, 8640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0]] 
 ![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]] where
  M :=![![![251, 0, 0], ![0, 251, 0], ![0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [165, 231, 176, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [143, 65, 153], [183, 185, 98], [0, 1]]
 g := ![![[133, 163, 245], [224, 214, 208], [22, 89], [7, 69, 67], [26, 0, 217], [220, 183, 103], [1]], ![[38, 138, 241, 190], [175, 75, 64, 140], [16, 232], [42, 214, 237, 112], [232, 102, 126, 245], [105, 223, 68, 135], [89, 10, 152, 58]], ![[112, 243, 215, 236], [60, 94, 155, 126], [79, 15], [195, 78, 117, 213], [19, 98, 142, 130], [49, 84, 59, 109], [185, 101, 152, 193]]]
 h' := ![![[143, 65, 153], [188, 32, 139], [95, 151, 220], [100, 77, 66], [228, 7, 148], [95, 175, 79], [86, 20, 75], [0, 1]], ![[183, 185, 98], [175, 188, 240], [107, 85, 49], [194, 78, 146], [23, 230, 88], [153, 43, 226], [181, 48, 118], [143, 65, 153]], ![[0, 1], [139, 31, 123], [198, 15, 233], [159, 96, 39], [34, 14, 15], [112, 33, 197], [168, 183, 58], [183, 185, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 23], []]
 b := ![[], [181, 248, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [165, 231, 176, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19315705, 7477290, -2802415]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76955, 29790, -11165]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀

instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![-58, 28, 1]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0], ![-58, 28, 1]] 
 ![![257, 0, 0], ![0, 257, 0], ![199, 28, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![-58, 28, 1], ![-352, 37, 139], ![-8126, 1025, -46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-199, -28, 257]], ![![-1, 0, 1], ![-109, -15, 139], ![4, 9, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [108, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [208, 256], [0, 1]]
 g := ![![[217, 185], [111], [193], [169], [36], [22], [88], [1]], ![[147, 72], [111], [193], [169], [36], [22], [88], [1]]]
 h' := ![![[208, 256], [172, 151], [248, 232], [180, 129], [106, 13], [216, 251], [104, 104], [149, 208], [0, 1]], ![[0, 1], [226, 106], [188, 25], [27, 128], [240, 244], [253, 6], [148, 153], [237, 49], [208, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [101, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [108, 49, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60258, -19714, 10916]
  a := ![-6, -2, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8218, -1266, 10916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0], ![118, 1, 0]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![257, 0, 0], ![118, 1, 0]] 
 ![![257, 0, 0], ![118, 1, 0], ![46, 0, 1]] where
  M :=![![![257, 0, 0], ![0, 257, 0], ![0, 0, 257]], ![![118, 1, 0], ![-2, 120, 5], ![-296, 39, 117]]]
  hmulB := by decide  
  f := ![![![54075, -3548923, -147870], ![11051, 7600518, 0]], ![![24796, -1629380, -67890], ![5141, 3489546, 0]], ![![9654, -635216, -26467], ![2032, 1360404, 0]]]
  g := ![![![1, 0, 0], ![-118, 257, 0], ![-46, 0, 257]], ![![0, 1, 0], ![-56, 120, 5], ![-40, 39, 117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![257, 0, 0], ![-58, 28, 1]] ![![257, 0, 0], ![118, 1, 0]]
  ![![257, 0, 0]] where
 M := ![![![66049, 0, 0], ![30326, 257, 0]], ![![-14906, 7196, 257], ![-7196, 3341, 257]]]
 hmul := by decide  
 g := ![![![![257, 0, 0]], ![![118, 1, 0]]], ![![![-58, 28, 1]], ![![-28, 13, 1]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)


lemma PB280I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 257 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 257 (by omega)

def PB280I4 : PrimesBelowBoundCertificateInterval O 193 257 280 where
  m := 11
  g := ![2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257]
  hP := PB280I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1]
    · exact ![I199N0, I199N1]
    · exact ![I211N0]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0]
    · exact ![I241N0]
    · exact ![I251N0]
    · exact ![I257N0, I257N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC197
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
    · exact PBC257
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![38809, 197]
    · exact ![39601, 199]
    · exact ![9393931]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![233, 233, 233]
    · exact ![13651919]
    · exact ![13997521]
    · exact ![15813251]
    · exact ![66049, 257]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
  β := ![I197N1, I199N1, I227N1, I229N1, I233N0, I233N1, I233N2, I257N1]
  Il := ![[I197N1], [I199N1], [], [], [I227N1], [I229N1], [I233N0, I233N1, I233N2], [], [], [], [I257N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
