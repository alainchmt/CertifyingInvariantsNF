
import IdealArithmetic.Examples.NF5_3_1518750000_3.RI5_3_1518750000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![689, -749, 167, -134, 62]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![689, -749, 167, -134, 62]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![1, 4, 1, 0, 0], ![23, 10, 0, 1, 0], ![2, 17, 0, 0, 1]] where
  M :=![![![689, -749, 167, -134, 62], ![-1488, 1619, -362, 288, -134], ![3216, -3498, 781, -624, 288], ![-2760, 3005, -671, 541, -248], ![888, -963, 211, -186, 85]]]
  hmulB := by decide  
  f := ![![![-3299, -157, 837, 302, 204]], ![![-4896, -239, 1236, 444, 302]], ![![-1039, -51, 262, 94, 64]], ![![-4241, -204, 1074, 387, 262]], ![![-3062, -150, 773, 278, 189]]]
  g := ![![![120, -39, 167, -134, 62], ![-258, 85, -362, 288, -134], ![559, -182, 781, -624, 288], ![-484, 155, -671, 541, -248], ![165, -48, 211, -186, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [13, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 28], [0, 1]]
 g := ![![[13, 9], [23], [1, 28], [5, 1]], ![[0, 20], [23], [25, 1], [10, 28]]]
 h' := ![![[5, 28], [15, 26], [16, 9], [22, 12], [0, 1]], ![[0, 1], [0, 3], [3, 20], [24, 17], [5, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [17, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [13, 24, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3899, 4433, -2474, -5662, 1717]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4323, 1440, -2474, -5662, 1717]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-853, 945, -219, 166, -80]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-853, 945, -219, 166, -80]] 
 ![![29, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-853, 945, -219, 166, -80], ![1920, -2053, 442, -372, 166], ![-3984, 4410, -1019, 780, -372], ![3480, -3799, 853, -683, 316], ![-1128, 1233, -281, 210, -107]]]
  hmulB := by decide  
  f := ![![![-3707609, -163127, 951331, 345170, 230918]], ![![-1597439, -70284, 409885, 148718, 99492]], ![![-3354024, -147570, 860605, 312252, 208896]], ![![-184034, -8097, 47221, 17133, 11462]], ![![-986336, -43397, 253083, 91826, 61431]]]
  g := ![![![-196, 945, -219, 166, -80], ![459, -2053, 442, -372, 166], ![-918, 4410, -1019, 780, -372], ![815, -3799, 853, -683, 316], ![-259, 1233, -281, 210, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-68099, 74080, -16540, 13247, -6131]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-68099, 74080, -16540, 13247, -6131]] 
 ![![29, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-68099, 74080, -16540, 13247, -6131], ![147144, -160064, 35737, -28623, 13247], ![-317928, 345849, -77218, 61845, -28623], ![273456, -297470, 66416, -53194, 24619], ![-88416, 96180, -21474, 17199, -7960]]]
  hmulB := by decide  
  f := ![![![401, -30, -150, -71, -39]], ![![295, -26, -107, -46, -28]], ![![280, -21, -106, -49, -21]], ![![93, 4, -46, -37, -14]], ![![245, -42, -72, -14, -43]]]
  g := ![![![-42275, 74080, -16540, 13247, -6131], ![91344, -160064, 35737, -28623, 13247], ![-197365, 345849, -77218, 61845, -28623], ![169757, -297470, 66416, -53194, 24619], ![-54887, 96180, -21474, 17199, -7960]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2

def I29N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, -19, -51, -21, -11]] i)))

def SI29N3: IdealEqSpanCertificate' Table ![![127, -19, -51, -21, -11]] 
 ![![29, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![127, -19, -51, -21, -11], ![264, -38, -107, -45, -21], ![504, -51, -230, -129, -45], ![-72, -3, 43, 34, 1], ![264, -117, -13, 111, -8]]]
  hmulB := by decide  
  f := ![![![-11581, 12467, -2755, 2241, -1025]], ![![-8736, 9388, -2071, 1689, -771]], ![![-3452, 3727, -826, 669, -307]], ![![-2803, 3002, -660, 541, -246]], ![![-2509, 2708, -600, 486, -223]]]
  g := ![![![37, -19, -51, -21, -11], ![76, -38, -107, -45, -21], ![148, -51, -230, -129, -45], ![-19, -3, 43, 34, 1], ![67, -117, -13, 111, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N3 : Nat.card (O ⧸ I29N3) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N3)

lemma isPrimeI29N3 : Ideal.IsPrime I29N3 := prime_ideal_of_norm_prime hp29.out _ NI29N3
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![689, -749, 167, -134, 62]] ![![-853, 945, -219, 166, -80]]
  ![![-3227381, 3510784, -783846, 627804, -290556]] where
 M := ![![![-3227381, 3510784, -783846, 627804, -290556]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-3227381, 3510784, -783846, 627804, -290556]] ![![-68099, 74080, -16540, 13247, -6131]]
  ![![1182945380623, -1286825401870, 287308419984, -230111921029, 106499185053]] where
 M := ![![![1182945380623, -1286825401870, 287308419984, -230111921029, 106499185053]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N2 : IdealMulLeCertificate' Table 
  ![![1182945380623, -1286825401870, 287308419984, -230111921029, 106499185053]] ![![127, -19, -51, -21, -11]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-555914543, 604731925, -135017939, 108139028, -50048316]]]
 hmul := by decide  
 g := ![![![![-19169467, 20852825, -4655791, 3728932, -1725804]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2, I29N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
    exact isPrimeI29N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1 ⊙ MulI29N2)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [26, 24, 26, 28, 24, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 20, 9, 1, 4], [17, 5, 5, 1, 26], [19, 20, 11, 29, 15], [30, 16, 6, 0, 17], [0, 1]]
 g := ![![[13, 26, 1], [24, 8, 10, 3, 14], [21, 7, 1], []], ![[27, 17, 8, 12, 1, 1, 29, 2], [17, 5, 5, 23, 4, 15, 2, 4], [0, 25, 13, 11, 25, 9, 25, 9], [7, 6, 25, 21, 28, 16, 0, 2]], ![[26, 4, 30, 12, 10, 1, 1, 30], [6, 26, 19, 4, 20, 0, 16, 23], [23, 1, 19, 15, 28, 0, 10, 6], [14, 2, 30, 21, 25, 27, 6, 30]], ![[5, 17, 20, 21, 29, 27, 2, 24], [17, 28, 10, 6, 12, 24, 21, 22], [10, 23, 23, 23, 21, 21, 9, 17], [20, 19, 17, 2, 24, 24, 17, 27]], ![[7, 13, 16, 1, 12, 14, 6, 30], [19, 11, 11, 21, 13, 18, 5, 23], [30, 22, 21, 1, 21, 25, 23, 29], [21, 7, 26, 11, 26, 30, 12, 15]]]
 h' := ![![[3, 20, 9, 1, 4], [27, 11, 6, 30], [12, 27, 4, 12, 18], [0, 0, 0, 1], [0, 1]], ![[17, 5, 5, 1, 26], [23, 20, 24, 30, 4], [0, 1, 26, 15, 30], [0, 30, 15, 4, 14], [3, 20, 9, 1, 4]], ![[19, 20, 11, 29, 15], [22, 16, 11, 4, 26], [25, 29, 30, 11, 13], [23, 10, 16, 3, 25], [17, 5, 5, 1, 26]], ![[30, 16, 6, 0, 17], [20, 5, 2, 13, 13], [16, 19, 18, 5, 7], [15, 9, 1, 12, 20], [19, 20, 11, 29, 15]], ![[0, 1], [29, 10, 19, 16, 19], [29, 17, 15, 19, 25], [11, 13, 30, 11, 3], [30, 16, 6, 0, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 6, 0, 15], [], [], []]
 b := ![[], [12, 2, 8, 2, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [26, 24, 26, 28, 24, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14815332853, 13330877672, -17294593379, -53665030837, 3563172302]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-477913963, 430028312, -557890109, -1731130027, 114941042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [32, 0, 27, 3, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 3, 2, 31, 36], [24, 24, 8, 18, 34], [4, 12, 18, 30, 9], [4, 34, 9, 32, 32], [0, 1]]
 g := ![![[29, 22, 16, 20, 36], [10, 4], [2, 27, 24, 29, 1], [], []], ![[14, 15, 9, 22, 3, 20, 2, 33], [1, 26, 27, 36], [25, 4, 11, 7, 34, 9, 10, 1], [10, 31, 18, 21], [29, 34, 4, 1]], ![[24, 5, 13, 23, 8, 8, 9, 21], [20, 25, 9, 33], [34, 10, 26, 24, 25, 14, 8, 25], [21, 8, 4, 7], [27, 24, 5, 9]], ![[17, 1, 21, 9, 5, 0, 14, 33], [21, 24, 31, 1], [24, 13, 24, 26, 17, 27, 24, 28], [9, 34, 20, 33], [28, 32, 3, 7]], ![[19, 32, 35, 11, 18, 9, 6, 6], [22, 14, 34, 28], [35, 36, 24, 15, 19, 13, 1, 29], [29, 2, 24, 34], [4, 24, 35, 25]]]
 h' := ![![[34, 3, 2, 31, 36], [2, 19, 35, 36, 31], [10, 24, 29, 2], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[24, 24, 8, 18, 34], [15, 13, 2, 17, 35], [26, 7, 2, 17, 6], [12, 18, 5, 1, 31], [6, 4, 11, 10, 13], [34, 3, 2, 31, 36]], ![[4, 12, 18, 30, 9], [10, 8, 25, 9, 17], [24, 23, 16, 16, 12], [21, 5, 8, 1, 2], [8, 14, 34, 9, 28], [24, 24, 8, 18, 34]], ![[4, 34, 9, 32, 32], [27, 4, 10, 27, 4], [25, 11, 26, 1, 1], [35, 11, 18, 6, 6], [8, 34, 28, 18, 12], [4, 12, 18, 30, 9]], ![[0, 1], [35, 30, 2, 22, 24], [6, 9, 1, 1, 18], [35, 3, 6, 29, 34], [36, 22, 0, 0, 21], [4, 34, 9, 32, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 33, 31, 6], [], [], []]
 b := ![[], [32, 28, 16, 6, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [32, 0, 27, 3, 8, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30355440359, -15793142160, 2787270273, 20794809116, 4628962626]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![820417307, -426841680, 75331629, 562021868, 125107098]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11035, 11986, -2672, 2145, -991]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-11035, 11986, -2672, 2145, -991]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![37, 18, 30, 1, 0], ![11, 8, 4, 0, 1]] where
  M :=![![![-11035, 11986, -2672, 2145, -991], ![23784, -25900, 5789, -4629, 2145], ![-51480, 55959, -12484, 10011, -4629], ![44256, -48132, 10744, -8608, 3983], ![-14304, 15564, -3476, 2781, -1288]]]
  hmulB := by decide  
  f := ![![![-59, 4, 26, 15, 5]], ![![-120, 16, 47, 21, 15]], ![![-360, 105, 76, -51, 21]], ![![-367, 86, 100, -13, 26]], ![![-65, 8, 26, 12, 7]]]
  g := ![![![-1939, -456, -1538, 2145, -991], ![4182, 982, 3319, -4629, 2145], ![-9048, -2127, -7178, 10011, -4629], ![7779, 1828, 6172, -8608, 3983], ![-2513, -590, -1994, 2781, -1288]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [17, 34, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 14, 16], [16, 26, 25], [0, 1]]
 g := ![![[32, 11, 36], [22, 32], [34, 32], [32, 5, 1], []], ![[10, 35, 11, 16], [19, 16], [37, 25], [15, 8, 10, 33], [6, 10]], ![[17, 7, 10, 10], [23, 37], [4, 33], [20, 7, 31, 21], [38, 10]]]
 h' := ![![[30, 14, 16], [31, 3, 6], [35, 39, 14], [30, 16, 14], [0, 0, 1], [0, 1]], ![[16, 26, 25], [30, 9, 40], [36, 18, 4], [38, 24, 5], [19, 15, 26], [30, 14, 16]], ![[0, 1], [35, 29, 36], [37, 25, 23], [33, 1, 22], [20, 26, 14], [16, 26, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 35], []]
 b := ![[], [39, 33, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [17, 34, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7192952, 4736409, -1446143, -6061388, -121225]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5327119, 2800273, 4411717, -6061388, -121225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, 4, 26, 15, 5]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-59, 4, 26, 15, 5]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![35, 28, 1, 0, 0], ![31, 32, 0, 1, 0], ![33, 38, 0, 0, 1]] where
  M :=![![![-59, 4, 26, 15, 5], ![-120, 16, 47, 21, 15], ![-360, 105, 76, -51, 21], ![96, -60, 12, 64, -19], ![384, -264, 100, 363, 28]]]
  hmulB := by decide  
  f := ![![![-11035, 11986, -2672, 2145, -991]], ![![23784, -25900, 5789, -4629, 2145]], ![![5567, -6091, 1368, -1086, 506]], ![![11299, -12326, 2760, -2201, 1022]], ![![12813, -13978, 3130, -2496, 1159]]]
  g := ![![![-39, -34, 26, 15, 5], ![-71, -62, 47, 21, 15], ![-52, -29, 76, -51, 21], ![-41, -42, 12, 64, -19], ![-373, -384, 100, 363, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 40], [0, 1]]
 g := ![![[12, 21], [20], [16], [7, 2], [1]], ![[0, 20], [20], [16], [0, 39], [1]]]
 h' := ![![[17, 40], [1, 12], [0, 15], [27, 37], [39, 17], [0, 1]], ![[0, 1], [0, 29], [9, 26], [0, 4], [0, 24], [17, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [4, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [2, 24, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7629, 7847, -4123, -10172, 2375]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9113, 8745, -4123, -10172, 2375]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-11035, 11986, -2672, 2145, -991]] ![![-59, 4, 26, 15, 5]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [39, 20, 30, 12, 32, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 22, 3, 9, 2], [33, 23, 17, 35, 24], [12, 38, 12, 40, 9], [10, 2, 11, 2, 8], [0, 1]]
 g := ![![[32, 1, 22, 3, 15], [5, 31, 20, 41, 40], [16, 8, 35, 35], [1], []], ![[33, 8, 29, 8, 8, 27, 9, 34], [22, 39, 6, 31, 36, 0, 6, 26], [34, 1, 30, 41], [40, 29, 28, 38, 14, 12, 8, 26], [35, 22, 37, 4]], ![[9, 8, 38, 3, 41, 13, 11, 41], [5, 20, 29, 28, 0, 13, 23, 23], [9, 19, 26, 23], [34, 23, 20, 9, 16, 35, 2, 4], [2, 14, 18, 17]], ![[40, 21, 30, 22, 36, 40, 2, 9], [7, 41, 4, 6, 32, 30, 22, 25], [7, 5, 16, 11], [14, 10, 31, 26, 3, 38, 10, 15], [14, 32, 20, 38]], ![[20, 30, 24, 2, 17, 15, 37, 39], [26, 5, 11, 26, 1, 16, 25, 3], [13, 35, 14, 4], [21, 38, 10, 26, 34, 30, 38, 19], [16, 26, 5, 21]]]
 h' := ![![[42, 22, 3, 9, 2], [20, 17, 42, 39, 31], [37, 25, 4, 26, 13], [4, 23, 13, 31, 11], [0, 0, 1], [0, 1]], ![[33, 23, 17, 35, 24], [20, 7, 6, 17, 24], [5, 13, 14, 27, 23], [16, 39, 26, 36, 27], [12, 32, 39, 30, 20], [42, 22, 3, 9, 2]], ![[12, 38, 12, 40, 9], [22, 11, 23, 1, 38], [24, 33, 19, 3, 32], [26, 20, 4, 29, 25], [22, 29, 7, 34, 6], [33, 23, 17, 35, 24]], ![[10, 2, 11, 2, 8], [40, 33, 39, 33, 1], [1, 40, 0, 33, 27], [4, 20, 13, 19, 21], [28, 29, 21, 23, 4], [12, 38, 12, 40, 9]], ![[0, 1], [32, 18, 19, 39, 35], [15, 18, 6, 40, 34], [36, 27, 30, 14, 2], [35, 39, 18, 42, 13], [10, 2, 11, 2, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 6, 31, 18], [], [], []]
 b := ![[], [27, 16, 31, 38, 34], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [39, 20, 30, 12, 32, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84864005145, 6477881544, 24993179992, -10693340792, -46799838792]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1973581515, 150648408, 581236744, -248682344, -1088368344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-185639, 200913, -44607, 36027, -16569]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-185639, 200913, -44607, 36027, -16569]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![24, 8, 34, 46, 1]] where
  M :=![![![-185639, 200913, -44607, 36027, -16569], ![397656, -434174, 97341, -77481, 36027], ![-864648, 938061, -208778, 168003, -77481], ![742248, -806841, 179997, -144338, 66741], ![-239688, 260901, -58263, 46647, -21596]]]
  hmulB := by decide  
  f := ![![![-121, 33, 15, -45, -45]], ![![1080, -796, 303, 1035, -45]], ![![1080, 405, -742, -477, 1035]], ![![-4680, 2565, -543, -3370, -597]], ![![-3648, 2567, -917, -3341, 46]]]
  g := ![![![4511, 7095, 11037, 16983, -16569], ![-9936, -15370, -23991, -36909, 36027], ![21168, 33147, 51608, 79407, -77481], ![-18288, -28527, -44451, -68392, 66741], ![5928, 9227, 14383, 22129, -21596]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [30, 42, 24, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 12, 35, 20], [25, 28, 6, 36], [34, 6, 6, 38], [0, 1]]
 g := ![![[45, 6, 38, 7], [7, 28, 28, 9], [27, 25, 18, 6], [25, 1], []], ![[44, 29, 34, 23, 42, 15], [38, 36, 10, 10, 26, 29], [39, 42, 29, 38, 12, 5], [0, 33, 8, 3, 31, 5], [40, 26, 24]], ![[28, 41, 22, 32, 33, 1], [2, 9, 13, 9, 28, 36], [9, 3, 1, 45, 36, 12], [36, 25, 31, 0, 6, 24], [33, 26, 27]], ![[23, 30, 24, 45, 23, 13], [11, 33, 22, 29, 41, 43], [46, 11, 20, 11, 31, 23], [5, 2, 18, 39, 6, 44], [37, 37, 34]]]
 h' := ![![[13, 12, 35, 20], [25, 21, 25, 17], [36, 0, 22, 3], [2, 1, 16, 37], [0, 0, 1], [0, 1]], ![[25, 28, 6, 36], [18, 7, 46, 41], [20, 15, 10, 28], [23, 22, 29, 23], [3, 14, 21, 23], [13, 12, 35, 20]], ![[34, 6, 6, 38], [35, 45, 0, 39], [28, 45, 10, 1], [18, 6, 13, 43], [11, 33, 35, 28], [25, 28, 6, 36]], ![[0, 1], [24, 21, 23, 44], [36, 34, 5, 15], [25, 18, 36, 38], [46, 0, 37, 43], [34, 6, 6, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [45, 43, 38], []]
 b := ![[], [], [25, 15, 1, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [30, 42, 24, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2334849073, 1402260669, -377556540, -1835599960, -187581357]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![46108585, 61764075, 127664034, 144534946, -187581357]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121, -33, -15, 45, 45]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![121, -33, -15, 45, 45]] 
 ![![47, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![121, -33, -15, 45, 45], ![-1080, 796, -303, -1035, 45], ![-1080, -405, 742, 477, -1035], ![4680, -2565, 543, 3370, 597], ![-1368, 5535, -4323, -7011, 4126]]]
  hmulB := by decide  
  f := ![![![185639, -200913, 44607, -36027, 16569]], ![![-4511, 4963, -1122, 882, -414]], ![![200086, -216597, 48100, -38835, 17865]], ![![110600, -119625, 26541, -21458, 9861]], ![![68296, -73947, 16425, -13257, 6100]]]
  g := ![![![-28, -33, -15, 45, 45], ![946, 796, -303, -1035, 45], ![-713, -405, 742, 477, -1035], ![-2875, -2565, 543, 3370, 597], ![7453, 5535, -4323, -7011, 4126]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-185639, 200913, -44607, 36027, -16569]] ![![121, -33, -15, 45, 45]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![-47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6881, -7502, 1670, -1391, 625]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![6881, -7502, 1670, -1391, 625]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![49, 46, 12, 6, 1]] where
  M :=![![![6881, -7502, 1670, -1391, 625], ![-15000, 16256, -3601, 2943, -1391], ![33384, -35865, 8074, -5397, 2943], ![-28464, 30854, -7040, 4642, -2371], ![4896, -7332, 1530, -4959, 472]]]
  hmulB := by decide  
  f := ![![![-14459, 2288, 6112, 2687, 1277]], ![![-30648, 4696, 12829, 5625, 2687]], ![![-64488, 9657, 26810, 11733, 5625]], ![![9744, -1514, -4096, -1798, -857]], ![![-53743, 8244, 22504, 9868, 4713]]]
  g := ![![![-448, -684, -110, -97, 625], ![1003, 1514, 247, 213, -1391], ![-2091, -3231, -514, -435, 2943], ![1655, 2640, 404, 356, -2371], ![-344, -548, -78, -147, 472]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [35, 33, 46, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 50, 50, 23], [29, 5, 39, 50], [6, 50, 17, 33], [0, 1]]
 g := ![![[51, 28, 29, 52], [19, 3, 25], [31, 21, 38, 25], [8, 52, 1], []], ![[31, 18, 36, 42, 12, 45], [36, 40, 10], [43, 41, 26, 37, 31, 34], [44, 35, 44], [45, 6, 14, 13, 32, 30]], ![[37, 4, 38, 45, 42, 45], [15, 9, 37], [19, 35, 40, 48, 12, 19], [42, 52, 4], [21, 44, 48, 17, 20, 26]], ![[34, 36, 49, 6, 6, 12], [4, 14, 16], [49, 45, 48, 30, 36, 20], [48, 38, 10], [4, 17, 34, 24, 45, 3]]]
 h' := ![![[17, 50, 50, 23], [13, 22, 4, 30], [28, 4, 29, 48], [38, 36, 1, 5], [0, 0, 0, 1], [0, 1]], ![[29, 5, 39, 50], [48, 40, 28, 48], [47, 46, 47, 40], [51, 32, 2, 38], [52, 50, 29, 37], [17, 50, 50, 23]], ![[6, 50, 17, 33], [1, 48, 27, 41], [7, 31, 13, 14], [5, 47, 35, 33], [16, 47, 14, 2], [29, 5, 39, 50]], ![[0, 1], [2, 49, 47, 40], [6, 25, 17, 4], [15, 44, 15, 30], [23, 9, 10, 13], [6, 50, 17, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [24, 19, 36], []]
 b := ![[], [], [46, 22, 33, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [35, 33, 46, 1, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19622952, 11895391, -3275181, -15594743, -1469738]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![988570, 1500063, 270975, -127855, -1469738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14459, -2288, -6112, -2687, -1277]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![14459, -2288, -6112, -2687, -1277]] 
 ![![53, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![14459, -2288, -6112, -2687, -1277], ![30648, -4696, -12829, -5625, -2687], ![64488, -9657, -26810, -11733, -5625], ![-9744, 1514, 4096, 1798, 857], ![14688, -2004, -5946, -2583, -1256]]]
  hmulB := by decide  
  f := ![![![-6881, 7502, -1670, 1391, -625]], ![![-5819, 6346, -1413, 1178, -528]], ![![-2837, 3083, -688, 548, -256]], ![![-4007, 4372, -970, 831, -368]], ![![-1910, 2120, -470, 461, -174]]]
  g := ![![![6374, -2288, -6112, -2687, -1277], ![13282, -4696, -12829, -5625, -2687], ![27614, -9657, -26810, -11733, -5625], ![-4254, 1514, 4096, 1798, 857], ![5999, -2004, -5946, -2583, -1256]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![6881, -7502, 1670, -1391, 625]] ![![14459, -2288, -6112, -2687, -1277]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5449, -6393, 1529, -1101, 553]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![5449, -6393, 1529, -1101, 553]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![0, 0, 0, 59, 0], ![9, 50, 40, 17, 1]] where
  M :=![![![5449, -6393, 1529, -1101, 553], ![-13272, 13744, -2917, 2523, -1101], ![26424, -29787, 6874, -5253, 2523], ![-23304, 25605, -5771, 4558, -2137], ![7800, -8331, 1843, -1413, 670]]]
  hmulB := by decide  
  f := ![![![14339, -2025, -5861, -2553, -1235]], ![![29640, -4186, -12115, -5277, -2553]], ![![61272, -8655, -25042, -10905, -5277]], ![![-9528, 1347, 3893, 1694, 821]], ![![66321, -9367, -27107, -11806, -5712]]]
  g := ![![![8, -577, -349, -178, 553], ![-57, 1166, 697, 360, -1101], ![63, -2643, -1594, -816, 2523], ![-69, 2245, 1351, 693, -2137], ![30, -709, -423, -217, 670]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 4 2 5 [50, 15, 21, 49, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 13, 27, 15], [6, 55, 17, 27], [7, 49, 15, 17], [0, 1]]
 g := ![![[39, 54, 23, 17], [44, 26, 7, 48], [56, 18, 48], [34, 20, 10, 1], []], ![[34, 51, 3, 19, 42, 51], [9, 10, 53, 32, 32, 53], [0, 42, 28], [29, 13, 10, 19, 44, 46], [10, 50, 3, 47, 55, 12]], ![[36, 43, 36, 30, 37, 1], [10, 48, 0, 15, 13, 35], [1, 12, 57], [45, 27, 46, 7, 18, 45], [41, 5, 40, 13, 15, 36]], ![[50, 40, 25, 55, 51, 15], [9, 32, 38, 23, 49, 12], [21], [32, 55, 0, 50, 33, 48], [44, 20, 51, 12, 8, 16]]]
 h' := ![![[56, 13, 27, 15], [42, 32, 49, 28], [35, 27, 2, 44], [11, 24, 20, 15], [0, 0, 0, 1], [0, 1]], ![[6, 55, 17, 27], [10, 14, 35, 26], [57, 35, 47, 34], [36, 19, 14, 21], [4, 2, 45, 19], [56, 13, 27, 15]], ![[7, 49, 15, 17], [4, 8, 39, 25], [54, 56, 39, 35], [24, 57, 52, 23], [54, 1, 14, 49], [6, 55, 17, 27]], ![[0, 1], [43, 5, 54, 39], [48, 0, 30, 5], [53, 18, 32], [31, 56, 0, 49], [7, 49, 15, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [17, 21, 30], []]
 b := ![[], [], [6, 53, 29, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 4
  hpos := by decide
  P := [50, 15, 21, 49, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9588512, -24368189, 17604047, 29929714, -15306428]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2497396, 12558529, 10675613, 4917610, -15306428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 12117361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14339, 2025, 5861, 2553, 1235]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-14339, 2025, 5861, 2553, 1235]] 
 ![![59, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-14339, 2025, 5861, 2553, 1235], ![-29640, 4186, 12115, 5277, 2553], ![-61272, 8655, 25042, 10905, 5277], ![9528, -1347, -3893, -1694, -821], ![-12984, 1827, 5315, 2325, 1120]]]
  hmulB := by decide  
  f := ![![![-5449, 6393, -1529, 1101, -553]], ![![-3654, 4318, -1039, 741, -375]], ![![-1002, 1155, -272, 201, -99]], ![![-898, 1083, -265, 184, -95]], ![![-4750, 5559, -1327, 957, -480]]]
  g := ![![![-3933, 2025, 5861, 2553, 1235], ![-8130, 4186, 12115, 5277, 2553], ![-16806, 8655, 25042, 10905, 5277], ![2614, -1347, -3893, -1694, -821], ![-3562, 1827, 5315, 2325, 1120]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![5449, -6393, 1529, -1101, 553]] ![![-14339, 2025, 5861, 2553, 1235]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-455, -187, 327, 222, -450]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-455, -187, 327, 222, -450]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![41, 52, 50, 1, 0], ![23, 30, 52, 0, 1]] where
  M :=![![![-455, -187, 327, 222, -450], ![10800, -7205, 2372, 9396, 222], ![-5328, 14130, -10373, -17952, 9396], ![-34920, 15537, -917, -20609, -7690], ![74472, -89529, 51031, 114966, -34283]]]
  hmulB := by decide  
  f := ![![![-5387, 637, 1045, 594, 228]], ![![-5472, -1967, 2266, 384, 594]], ![![-14256, 3438, 2071, 1752, 384]], ![![-19879, 1518, 4332, 2149, 976]], ![![-16873, 2222, 3266, 1908, 703]]]
  g := ![![![13, 29, 207, 222, -450], ![-6222, -8237, -7852, 9396, 222], ![8436, 10914, 6535, -17952, 9396], ![16179, 21605, 23433, -20609, -7690], ![-63125, -82611, -64173, 114966, -34283]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [23, 43, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 58, 8], [56, 2, 53], [0, 1]]
 g := ![![[50, 28, 39], [6, 46], [43, 8, 27], [40, 25, 16], [1]], ![[29, 9, 21, 21], [52, 34], [12, 52, 59, 53], [51, 13, 25, 2], [32, 29, 8, 24]], ![[55, 38, 32, 23], [18, 60], [1, 16, 25, 21], [10, 51, 45, 24], [0, 30, 44, 37]]]
 h' := ![![[9, 58, 8], [31, 18, 10], [48, 5, 31], [56, 3, 24], [38, 18, 4], [0, 1]], ![[56, 2, 53], [11, 44, 42], [29, 57, 41], [0, 31, 11], [54, 34, 30], [9, 58, 8]], ![[0, 1], [33, 60, 9], [52, 60, 50], [30, 27, 26], [58, 9, 27], [56, 2, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 59], []]
 b := ![[], [2, 39, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [23, 43, 57, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1771964, 1377975, -558349, -1788059, 144720]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1118195, 1475663, 1333101, -1788059, 144720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-223, 138, -8, 34, -6]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-223, 138, -8, 34, -6]] 
 ![![61, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-223, 138, -8, 34, -6], ![144, -313, 104, -42, 34], ![-816, 654, -95, 138, -42], ![576, -568, 114, -107, 44], ![-144, 186, -48, 30, -17]]]
  hmulB := by decide  
  f := ![![![-1315, 182, 540, 238, 110]], ![![-690, 95, 284, 126, 58]], ![![-417, 60, 169, 72, 36]], ![![-183, 26, 74, 31, 14]], ![![-352, 38, 156, 82, 27]]]
  g := ![![![-73, 138, -8, 34, -6], ![128, -313, 104, -42, 34], ![-321, 654, -95, 138, -42], ![265, -568, 114, -107, 44], ![-82, 186, -48, 30, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4363, -631, -1797, -784, -378]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![4363, -631, -1797, -784, -378]] 
 ![![61, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![4363, -631, -1797, -784, -378], ![9072, -1307, -3726, -1626, -784], ![18816, -2688, -7723, -3366, -1626], ![-2904, 415, 1197, 521, 252], ![4056, -567, -1655, -720, -349]]]
  hmulB := by decide  
  f := ![![![-377, 197, -35, -256, -56]], ![![-219, 106, -13, -138, -40]], ![![76, -28, -3, 38, 22]], ![![-357, 208, -52, -271, -34]], ![![-492, 171, 29, -228, -151]]]
  g := ![![![1240, -631, -1797, -784, -378], ![2571, -1307, -3726, -1626, -784], ![5314, -2688, -7723, -3366, -1626], ![-822, 415, 1197, 521, 252], ![1133, -567, -1655, -720, -349]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-455, -187, 327, 222, -450]] ![![-223, 138, -8, 34, -6]]
  ![![377, -197, 35, 256, 56]] where
 M := ![![![377, -197, 35, 256, 56]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![377, -197, 35, 256, 56]] ![![4363, -631, -1797, -784, -378]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB1906I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1906I1 : PrimesBelowBoundCertificateInterval O 23 61 1906 where
  m := 9
  g := ![4, 1, 1, 2, 1, 2, 2, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1906I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2, I29N3]
    · exact ![I31N0]
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![841, 29, 29, 29]
    · exact ![28629151]
    · exact ![69343957]
    · exact ![68921, 1681]
    · exact ![147008443]
    · exact ![4879681, 47]
    · exact ![7890481, 53]
    · exact ![12117361, 59]
    · exact ![226981, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
      exact NI29N3
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
  β := ![I29N0, I29N1, I29N2, I29N3, I41N1, I47N1, I53N1, I59N1, I61N1, I61N2]
  Il := ![[I29N0, I29N1, I29N2, I29N3], [], [], [I41N1], [], [I47N1], [I53N1], [I59N1], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
