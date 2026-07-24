
import IdealArithmetic.Examples.NF3_1_730732_1.RI3_1_730732_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![598, 189, -33]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![598, 189, -33]] 
 ![![197, 0, 0], ![53, 1, 0], ![172, 0, 1]] where
  M :=![![![598, 189, -33], ![3687, 1786, 345], ![-17691, -4461, 1975]]]
  hmulB := by decide  
  f := ![![![-5066395, 226062, -124143]], ![![-1295095, 57787, -31734]], ![![-4500347, 200805, -110273]]]
  g := ![![![-19, 189, -33], ![-763, 1786, 345], ![-614, -4461, 1975]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N0 : Nat.card (O ⧸ I197N0) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N0)

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := prime_ideal_of_norm_prime hp197.out _ NI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-471714, -239547, -53900]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-471714, -239547, -53900]] 
 ![![197, 0, 0], ![68, 1, 0], ![151, 0, 1]] where
  M :=![![![-471714, -239547, -53900], ![5473853, 1468686, -532994], ![29218882, 12450592, 1229139]]]
  hmulB := by decide  
  f := ![![![8441310073802, -376650348767, 206839289118]], ![![2800545533113, -124960040866, 68622387064]], ![![6598361261858, -294418170739, 161681106465]]]
  g := ![![![121606, -239547, -53900], ![-70633, 1468686, -532994], ![-5091479, 12450592, 1229139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20593862, -4757255, 2684091]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-20593862, -4757255, 2684091]] 
 ![![197, 0, 0], ![75, 1, 0], ![143, 0, 1]] where
  M :=![![![-20593862, -4757255, 2684091], ![-289270901, -117221138, -6830419], ![313698569, -19309281, -121978393]]]
  hmulB := by decide  
  f := ![![![-14166555559052495, 632110187339786, -347126246455403]], ![![-5203371444757993, 232173874943279, -127499362212848]], ![![-10498351072610104, 468435297176095, -257243420012390]]]
  g := ![![![-241750, -4757255, 2684091], ![48117078, -117221138, -6830419], ![97486319, -19309281, -121978393]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![598, 189, -33]] ![![-471714, -239547, -53900]]
  ![![-211749861, -276536988, -173529653]] where
 M := ![![![-211749861, -276536988, -173529653]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-211749861, -276536988, -173529653]] ![![-20593862, -4757255, 2684091]]
  ![![197, 0, 0]] where
 M := ![![![29918847269372813, 36774061349053392, 22487375811664250]]]
 hmul := by decide  
 g := ![![![![151872321164329, 186670362177936, 114149115795250]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)
instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-63, -31, 1]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-63, -31, 1]] 
 ![![199, 0, 0], ![0, 199, 0], ![136, 168, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-63, -31, 1], ![-137, -99, -61], ![3215, 1045, -130]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -168, 199]], ![![-1, -1, 1], ![41, 51, -61], ![105, 115, -130]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [168, 180, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 198], [0, 1]]
 g := ![![[129, 13], [178, 81], [159, 31], [139], [57], [36], [19, 1]], ![[177, 186], [125, 118], [151, 168], [139], [57], [36], [38, 198]]]
 h' := ![![[19, 198], [145, 49], [153, 190], [63, 164], [172, 138], [185, 183], [191, 193], [0, 1]], ![[0, 1], [81, 150], [181, 9], [194, 35], [8, 61], [80, 16], [77, 6], [19, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [94, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [168, 180, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-718, -606, -494]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![334, 414, -494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![61, 1, 0]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![61, 1, 0]] 
 ![![199, 0, 0], ![61, 1, 0], ![130, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![61, 1, 0], ![1, 61, 2], ![-106, -36, 62]]]
  hmulB := by decide  
  f := ![![![-61, -3782, -124], ![0, 12338, 0]], ![![-19, -1159, -38], ![1, 3781, 0]], ![![-61, -2471, -81], ![69, 8060, 0]]]
  g := ![![![1, 0, 0], ![-61, 199, 0], ![-130, 0, 199]], ![![0, 1, 0], ![-20, 61, 2], ![-30, -36, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![199, 0, 0], ![-63, -31, 1]] ![![199, 0, 0], ![61, 1, 0]]
  ![![199, 0, 0]] where
 M := ![![![39601, 0, 0], ![12139, 199, 0]], ![![-12537, -6169, 199], ![-3980, -1990, 0]]]
 hmul := by decide  
 g := ![![![![199, 0, 0]], ![![61, 1, 0]]], ![![![-63, -31, 1]], ![![-20, -10, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3822, 685, -673]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![3822, 685, -673]] 
 ![![211, 0, 0], ![16, 1, 0], ![189, 0, 1]] where
  M :=![![![3822, 685, -673], ![72023, 28050, 697], ![-24827, 23123, 28735]]]
  hmulB := by decide  
  f := ![![![789900019, -35245254, 19355095]], ![![50007180, -2231315, 1225337]], ![![718734070, -32069837, 17611300]]]
  g := ![![![569, 685, -673], ![-2410, 28050, 697], ![-27610, 23123, 28735]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N0 : Nat.card (O ⧸ I211N0) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N0)

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := prime_ideal_of_norm_prime hp211.out _ NI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![204, -9, 5]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![204, -9, 5]] 
 ![![211, 0, 0], ![56, 1, 0], ![15, 0, 1]] where
  M :=![![![204, -9, 5], ![-539, 24, -13], ![599, -31, 15]]]
  hmulB := by decide  
  f := ![![![-43, -20, -3]], ![![-10, -5, -1]], ![![8, 3, 0]]]
  g := ![![![3, -9, 5], ![-8, 24, -13], ![10, -31, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3254266, 145205, -79740]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![-3254266, 145205, -79740]] 
 ![![211, 0, 0], ![138, 1, 0], ![79, 0, 1]] where
  M :=![![![-3254266, 145205, -79740], ![8597645, -383626, 210670], ![-9730190, 434160, -238421]]]
  hmulB := by decide  
  f := ![![![-7346, -2905, -110]], ![![-4763, -1916, -100]], ![![-1254, -555, -71]]]
  g := ![![![-80536, 145205, -79740], ![212773, -383626, 210670], ![-240801, 434160, -238421]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![3822, 685, -673]] ![![204, -9, 5]]
  ![![7346, 2905, 110]] where
 M := ![![![7346, 2905, 110]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![7346, 2905, 110]] ![![-3254266, 145205, -79740]]
  ![![211, 0, 0]] where
 M := ![![![-211, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
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


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [3, 38, 133, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 117, 16], [55, 105, 207], [0, 1]]
 g := ![![[137, 24, 179], [42, 14, 101], [145, 71, 101], [216, 109, 139], [213, 47, 58], [86, 72], [1]], ![[220, 192, 139, 82], [106, 167, 187, 4], [1, 101, 146, 179], [161, 18, 93, 156], [40, 3, 170, 178], [82, 63], [216, 68, 8, 82]], ![[21, 24, 86, 42], [52, 21, 132, 6], [194, 43, 205, 180], [153, 201, 184, 23], [195, 19, 3, 145], [8, 144], [105, 25, 116, 141]]]
 h' := ![![[35, 117, 16], [97, 44, 25], [11, 70, 18], [21, 170, 205], [30, 23, 94], [197, 89, 110], [220, 185, 90], [0, 1]], ![[55, 105, 207], [134, 202, 207], [23, 44, 111], [158, 161, 161], [170, 43, 203], [133, 202, 40], [80, 93, 145], [35, 117, 16]], ![[0, 1], [129, 200, 214], [206, 109, 94], [92, 115, 80], [23, 157, 149], [26, 155, 73], [148, 168, 211], [55, 105, 207]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 217], []]
 b := ![[], [71, 78, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [3, 38, 133, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![740806, 299489, 42816]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3322, 1343, 192]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42000947, -17568934, -1476765]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-42000947, -17568934, -1476765]] 
 ![![227, 0, 0], ![0, 227, 0], ![44, 147, 1]] where
  M :=![![![-42000947, -17568934, -1476765], ![138968156, 11162593, -36614633], ![1967157319, 737331939, -6406341]]]
  hmulB := by decide  
  f := ![![![-118615096777362, 5292592877127, -2906451970321]], ![![313376501731153, -13982825845806, 7678733783933]], ![![178381606789396, -7959368134025, 4370923993724]]]
  g := ![![![101219, 878923, -1476765], ![7709304, 23759972, -36614633], ![9907649, 7396758, -6406341]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [51, 197, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 226], [0, 1]]
 g := ![![[173, 108], [63, 134], [29], [173], [59], [85, 76], [30, 1]], ![[8, 119], [224, 93], [29], [173], [59], [95, 151], [60, 226]]]
 h' := ![![[30, 226], [192, 73], [93, 19], [133, 211], [199, 20], [205, 112], [59, 168], [0, 1]], ![[0, 1], [112, 154], [209, 208], [107, 16], [118, 207], [160, 115], [105, 59], [30, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [2, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [51, 197, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-303812, -304457, -161368]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29940, 103157, -161368]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![118615096777362, -5292592877127, 2906451970321]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![118615096777362, -5292592877127, 2906451970321]] 
 ![![227, 0, 0], ![159, 1, 0], ![72, 0, 1]] where
  M :=![![![118615096777362, -5292592877127, 2906451970321], ![-313376501731153, 13982825845806, -7678733783933], ![354656755082671, -15824746316219, 8690232968679]]]
  hmulB := by decide  
  f := ![![![42000947, 17568934, 1476765]], ![![28806971, 12256819, 1195684]], ![![4655995, 2324367, 496623]]]
  g := ![![![3307809790209, -5292592877127, 2906451970321], ![-8739105633353, 13982825845806, -7678733783933], ![9890284782452, -15824746316219, 8690232968679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-42000947, -17568934, -1476765]] ![![118615096777362, -5292592877127, 2906451970321]]
  ![![227, 0, 0]] where
 M := ![![![-227, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-278, -129, -21]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-278, -129, -21]] 
 ![![229, 0, 0], ![0, 229, 0], ![155, 137, 1]] where
  M :=![![![-278, -129, -21], ![2097, 478, -279], ![15165, 6135, 349]]]
  hmulB := by decide  
  f := ![![![8203, -366, 201]], ![![-21672, 967, -531]], ![![-7306, 326, -179]]]
  g := ![![![13, 12, -21], ![198, 169, -279], ![-170, -182, 349]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [125, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [217, 228], [0, 1]]
 g := ![![[132, 11], [5], [193, 215], [129], [12], [227, 132], [217, 1]], ![[0, 218], [5], [132, 14], [129], [12], [17, 97], [205, 228]]]
 h' := ![![[217, 228], [50, 195], [149, 163], [202, 131], [86, 75], [21, 87], [126, 19], [0, 1]], ![[0, 1], [0, 34], [25, 66], [4, 98], [102, 154], [122, 142], [127, 210], [217, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [211]]
 b := ![[], [175, 220]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [125, 12, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-609, -1407, -948]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![639, 561, -948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8203, -366, 201]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![8203, -366, 201]] 
 ![![229, 0, 0], ![183, 1, 0], ![202, 0, 1]] where
  M :=![![![8203, -366, 201], ![-21672, 967, -531], ![24525, -1095, 601]]]
  hmulB := by decide  
  f := ![![![-278, -129, -21]], ![![-213, -101, -18]], ![![-179, -87, -17]]]
  g := ![![![151, -366, 201], ![-399, 967, -531], ![452, -1095, 601]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-278, -129, -21]] ![![8203, -366, 201]]
  ![![229, 0, 0]] where
 M := ![![![229, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![131, -100, 1]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0], ![131, -100, 1]] 
 ![![233, 0, 0], ![0, 233, 0], ![131, 133, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![131, -100, 1], ![-206, 95, -199], ![10529, 3529, -5]]]
  hmulB := by decide  
  f := ![![![-130, 100, -1], ![233, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-131, -133, 233]], ![![0, -1, 1], ![111, 114, -199], ![48, 18, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [121, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [165, 232], [0, 1]]
 g := ![![[41, 52], [4], [2], [125, 16], [214], [215, 184], [165, 1]], ![[0, 181], [4], [2], [202, 217], [214], [52, 49], [97, 232]]]
 h' := ![![[165, 232], [15, 127], [158, 2], [20, 85], [6, 4], [81, 133], [73, 76], [0, 1]], ![[0, 1], [0, 106], [22, 231], [65, 148], [200, 229], [124, 100], [31, 157], [165, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [217, 164]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [121, 68, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-653, -494, -270]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![149, 152, -270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0], ![-34, 1, 0]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![233, 0, 0], ![-34, 1, 0]] 
 ![![233, 0, 0], ![199, 1, 0], ![5, 0, 1]] where
  M :=![![![233, 0, 0], ![0, 233, 0], ![0, 0, 233]], ![![-34, 1, 0], ![1, -34, 2], ![-106, -36, -33]]]
  hmulB := by decide  
  f := ![![![-32426, 1151028, -67710], ![9786, 7888215, 0]], ![![-27689, 983040, -57828], ![8389, 6736962, 0]], ![![-690, 24700, -1453], ![250, 169275, 0]]]
  g := ![![![1, 0, 0], ![-199, 233, 0], ![-5, 0, 233]], ![![-1, 1, 0], ![29, -34, 2], ![31, -36, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![233, 0, 0], ![131, -100, 1]] ![![233, 0, 0], ![-34, 1, 0]]
  ![![233, 0, 0]] where
 M := ![![![54289, 0, 0], ![-7922, 233, 0]], ![![30523, -23300, 233], ![-4660, 3495, -233]]]
 hmul := by decide  
 g := ![![![![233, 0, 0]], ![![-34, 1, 0]]], ![![![131, -100, 1]], ![![-20, 15, -1]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15999, -714, 392]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![15999, -714, 392]] 
 ![![239, 0, 0], ![0, 239, 0], ![128, 75, 1]] where
  M :=![![![15999, -714, 392], ![-42266, 1887, -1036], ![47852, -2128, 1173]]]
  hmulB := by decide  
  f := ![![![37, 14, 0]], ![![14, 37, 28]], ![![18, 17, 9]]]
  g := ![![![-143, -126, 392], ![378, 333, -1036], ![-428, -377, 1173]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [43, 217, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 238], [0, 1]]
 g := ![![[144, 45], [212, 101], [78, 165], [118, 116], [160], [220, 174], [22, 1]], ![[178, 194], [44, 138], [123, 74], [41, 123], [160], [224, 65], [44, 238]]]
 h' := ![![[22, 238], [205, 146], [231, 36], [184, 167], [13, 127], [100, 87], [10, 202], [0, 1]], ![[0, 1], [71, 93], [67, 203], [34, 72], [178, 112], [102, 152], [152, 37], [22, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144]]
 b := ![[], [164, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [43, 217, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11881, -544, 1175]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-679, -371, 1175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -14, 0]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-37, -14, 0]] 
 ![![239, 0, 0], ![88, 1, 0], ![72, 0, 1]] where
  M :=![![![-37, -14, 0], ![-14, -37, -28], ![1484, 504, -51]]]
  hmulB := by decide  
  f := ![![![-15999, 714, -392]], ![![-5714, 255, -140]], ![![-5020, 224, -123]]]
  g := ![![![5, -14, 0], ![22, -37, -28], ![-164, 504, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![15999, -714, 392]] ![![-37, -14, 0]]
  ![![239, 0, 0]] where
 M := ![![![-239, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
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


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [205, 132, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 15, 4], [133, 225, 237], [0, 1]]
 g := ![![[29, 7, 182], [175, 194], [149, 10], [120, 82], [125, 37, 181], [34, 141, 61], [1]], ![[1, 57, 22, 45], [2, 96], [117, 183], [141, 113], [179, 132, 192, 108], [76, 226, 38, 54], [135, 152, 133, 64]], ![[40, 172, 85, 161], [156, 122], [160, 143], [27, 5], [81, 187, 12, 183], [179, 129, 142, 98], [91, 199, 60, 177]]]
 h' := ![![[80, 15, 4], [82, 147, 69], [224, 110, 215], [198, 4, 144], [162, 135, 75], [19, 197, 120], [36, 109, 213], [0, 1]], ![[133, 225, 237], [190, 36, 207], [212, 204, 133], [196, 60, 122], [120, 97, 63], [167, 63, 73], [156, 189, 161], [80, 15, 4]], ![[0, 1], [167, 58, 206], [24, 168, 134], [17, 177, 216], [238, 9, 103], [120, 222, 48], [138, 184, 108], [133, 225, 237]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 92], []]
 b := ![[], [223, 208, 218], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [205, 132, 28, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![65070, -28920, -46995]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![270, -120, -195]
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



lemma PB242I4_primes (p : ℕ) :
  p ∈ Set.range ![197, 199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 193 < p ∧ p ≤ 241 := by
  rw [← List.mem_ofFn']
  convert primes_range 193 241 (by omega)

def PB242I4 : PrimesBelowBoundCertificateInterval O 193 241 242 where
  m := 9
  g := ![3, 2, 3, 1, 2, 2, 2, 2, 1]
  P := ![197, 199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB242I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I197N0, I197N1, I197N2]
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![197, 197, 197]
    · exact ![39601, 199]
    · exact ![211, 211, 211]
    · exact ![11089567]
    · exact ![51529, 227]
    · exact ![52441, 229]
    · exact ![54289, 233]
    · exact ![57121, 239]
    · exact ![13997521]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
  β := ![I197N0, I197N1, I197N2, I199N1, I211N0, I211N1, I211N2, I227N1, I229N1, I233N1, I239N1]
  Il := ![[I197N0, I197N1, I197N2], [I199N1], [I211N0, I211N1, I211N2], [], [I227N1], [I229N1], [I233N1], [I239N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
