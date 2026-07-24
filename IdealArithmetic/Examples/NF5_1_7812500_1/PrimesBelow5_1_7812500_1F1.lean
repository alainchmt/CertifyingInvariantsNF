
import IdealArithmetic.Examples.NF5_1_7812500_1.RI5_1_7812500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 5 2 4 [20, 15, 4, 18, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 13, 12, 2, 26], [26, 3, 14, 1, 19], [5, 20, 13, 12, 4], [2, 21, 19, 14, 9], [0, 1]]
 g := ![![[8, 9, 17, 16, 5], [17, 4, 17, 5], [16, 18, 1], []], ![[17, 10, 3, 5, 7, 10, 23, 12], [21, 27, 28, 22], [22, 28, 11, 11, 16, 27, 14, 11], [3, 12, 15, 22, 8, 16, 3, 2]], ![[26, 10, 27, 27, 6, 9, 10, 15], [17, 11, 6, 6], [24, 8, 4, 12, 20, 20, 15, 15], [18, 26, 23, 24, 6, 8, 19, 15]], ![[2, 28, 7, 18, 26, 21, 20, 4], [27, 16, 15, 13], [23, 26, 6, 28, 15, 0, 6, 4], [2, 1, 18, 11, 5, 27, 17, 6]], ![[15, 12, 14, 20, 25, 27, 21, 6], [22, 9, 6, 22], [26, 17, 20, 22, 26, 1, 24, 20], [25, 3, 13, 8, 22, 14, 23, 4]]]
 h' := ![![[14, 13, 12, 2, 26], [9, 24, 2, 23, 11], [28, 9, 23, 2, 18], [0, 0, 0, 1], [0, 1]], ![[26, 3, 14, 1, 19], [14, 25, 26, 11, 5], [12, 27, 12, 9, 15], [16, 22, 3, 21, 8], [14, 13, 12, 2, 26]], ![[5, 20, 13, 12, 4], [17, 21, 25, 4, 19], [3, 15, 11, 10, 21], [19, 16, 13, 17, 10], [26, 3, 14, 1, 19]], ![[2, 21, 19, 14, 9], [7, 20, 15, 21, 1], [24, 27, 24, 24, 19], [27, 0, 9, 17, 28], [5, 20, 13, 12, 4]], ![[0, 1], [11, 26, 19, 28, 22], [4, 9, 17, 13, 14], [1, 20, 4, 2, 12], [2, 21, 19, 14, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 0, 3, 24], [], [], []]
 b := ![[], [22, 24, 5, 17, 8], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 5
  hpos := by decide
  P := [20, 15, 4, 18, 11, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142332841, -141773373, 153827397, 136775020, -699221349]
  a := ![5, -3, 16, 11, -45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4908029, -4888737, 5304393, 4716380, -24111081]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 20511149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -1, -2, 7, -10]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![21, -1, -2, 7, -10]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![11, 4, 12, 1, 0], ![18, 6, 21, 0, 1]] where
  M :=![![![21, -1, -2, 7, -10], ![-14, 38, -30, -27, 76], ![54, -117, 75, 29, -106], ![-58, 189, -108, 36, -8], ![4, 4, -2, 8, -15]]]
  hmulB := by decide  
  f := ![![![7, -17, -16, -7, 26]], ![![14, -26, -20, -7, 4]], ![![14, 3, 15, 11, -106]], ![![9, -4, 2, 3, -42]], ![![16, -11, -1, 3, -61]]]
  g := ![![![4, 1, 4, 7, -10], ![-35, -10, -42, -27, 76], ![53, 13, 63, 29, -106], ![-10, 3, -12, 36, -8], ![6, 2, 7, 8, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [4, 8, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 3, 10], [25, 27, 21], [0, 1]]
 g := ![![[4, 8, 28], [14, 24, 2], [21, 27, 19], [1]], ![[16, 21, 27, 7], [17, 3, 13, 2], [27, 14, 23, 20], [3, 0, 11, 8]], ![[14, 15, 8, 3], [2, 19, 29, 3], [24, 5, 30, 24], [25, 7, 30, 23]]]
 h' := ![![[15, 3, 10], [6, 28, 20], [9, 19, 23], [27, 23, 9], [0, 1]], ![[25, 27, 21], [15, 27, 14], [12, 24, 5], [15, 17, 8], [15, 3, 10]], ![[0, 1], [30, 7, 28], [29, 19, 3], [25, 22, 14], [25, 27, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 2], []]
 b := ![[], [23, 3, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [4, 8, 22, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![70841855, -104121559, 19027077, 21965669, -197913666]
  a := ![59, -60, 177, 116, -528]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![109408564, 32112831, 126181485, 21965669, -197913666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![225, 11, -67, -44, 174]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![225, 11, -67, -44, 174]] 
 ![![31, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![225, 11, -67, -44, 174], ![88, 7, -29, -21, 78], ![42, -11, -2, -2, 12], ![4, 28, -21, -4, 24], ![38, 3, -12, -7, 29]]]
  hmulB := by decide  
  f := ![![![17, 64, 91, 51, -354]], ![![0, 26, 31, 16, -96]], ![![2, 84, 102, 53, -324]], ![![-4, 87, 101, 51, -294]], ![![-6, 31, 32, 15, -73]]]
  g := ![![![59, 11, -67, -44, 174], ![26, 7, -29, -21, 78], ![4, -11, -2, -2, 12], ![10, 28, -21, -4, 24], ![10, 3, -12, -7, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235, -11, 70, 47, -184]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-235, -11, 70, 47, -184]] 
 ![![31, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-235, -11, 70, 47, -184], ![-94, -4, 28, 19, -74], ![-38, -1, 11, 7, -28], ![-14, -3, 6, 4, -14], ![-40, -2, 12, 8, -31]]]
  hmulB := by decide  
  f := ![![![-1, 13, 12, 9, -40]], ![![-1, 7, 6, 4, -18]], ![![-1, 8, 9, 6, -24]], ![![-3, 14, 8, 7, -26]], ![![-1, 5, 4, 3, -11]]]
  g := ![![![-17, -11, 70, 47, -184], ![-7, -4, 28, 19, -74], ![-3, -1, 11, 7, -28], ![-1, -3, 6, 4, -14], ![-3, -2, 12, 8, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![21, -1, -2, 7, -10]] ![![225, 11, -67, -44, 174]]
  ![![4201, 412, -1401, -857, 3430]] where
 M := ![![![4201, 412, -1401, -857, 3430]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![4201, 412, -1401, -857, 3430]] ![![-235, -11, 70, 47, -184]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-1097927, -50747, 326213, 219480, -858576]]]
 hmul := by decide  
 g := ![![![![-35417, -1637, 10523, 7080, -27696]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, -73, 90, 101, -286]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-67, -73, 90, 101, -286]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![34, 26, 9, 36, 1]] where
  M :=![![![-67, -73, 90, 101, -286], ![-202, 320, -208, -129, 388], ![258, -719, 447, 49, -382], ![-98, 689, -298, 584, -1028], ![12, -30, 38, 78, -189]]]
  hmulB := by decide  
  f := ![![![-3, -15, -20, -11, 74]], ![![22, -88, -86, -39, 172]], ![![78, -189, -159, -63, 158]], ![![126, -143, -64, -2, -344]], ![![156, -263, -181, -55, -111]]]
  g := ![![![261, 199, 72, 281, -286], ![-362, -264, -100, -381, 388], ![358, 249, 105, 373, -382], ![942, 741, 242, 1016, -1028], ![174, 132, 47, 186, -189]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 4 2 5 [30, 34, 10, 23, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 27, 28, 8], [20, 28, 20, 9], [26, 18, 26, 20], [0, 1]]
 g := ![![[6, 3, 25, 9], [13, 30, 21], [6, 12, 22, 11], [1], []], ![[29, 21, 21, 7, 25, 24], [8, 4, 1], [3, 19, 10, 13, 22, 24], [29, 12, 28], [4, 12, 27]], ![[27, 34, 7, 28, 1, 16], [10, 10, 26], [13, 3, 23, 35, 25, 3], [4, 18, 28], [31, 14, 7]], ![[26, 5, 14, 19, 13, 22], [22, 36, 3], [7, 22, 5, 32, 20, 32], [12], [2, 17, 30]]]
 h' := ![![[5, 27, 28, 8], [5, 20, 23, 34], [5, 3, 24, 13], [7, 3, 27, 14], [0, 0, 1], [0, 1]], ![[20, 28, 20, 9], [20, 26, 24, 22], [36, 13, 5, 36], [15, 6, 19, 15], [16, 33, 10, 18], [5, 27, 28, 8]], ![[26, 18, 26, 20], [8, 13, 24, 26], [30, 30, 23, 10], [24, 13, 7, 5], [25, 16, 33, 19], [20, 28, 20, 9]], ![[0, 1], [17, 15, 3, 29], [23, 28, 22, 15], [31, 15, 21, 3], [24, 25, 30], [26, 18, 26, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 6, 4], []]
 b := ![[], [], [16, 32, 7, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 4
  hpos := by decide
  P := [30, 34, 10, 23, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1041150, -1088280, 1380856, 725708, -5131224]
  a := ![4, -3, 13, 8, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4743318, 3576312, 1285456, 5012156, -5131224]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1874161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 15, 20, 11, -74]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![3, 15, 20, 11, -74]] 
 ![![37, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![3, 15, 20, 11, -74], ![-22, 88, 86, 39, -172], ![-78, 189, 159, 63, -158], ![-126, 143, 64, 2, 344], ![-64, 84, 46, 8, 133]]]
  hmulB := by decide  
  f := ![![![67, 73, -90, -101, 286]], ![![29, 17, -26, -32, 90]], ![![22, 51, -51, -45, 134]], ![![28, 9, -26, -54, 136]], ![![54, 60, -74, -84, 237]]]
  g := ![![![42, 15, 20, 11, -74], ![56, 88, 86, 39, -172], ![-33, 189, 159, 63, -158], ![-361, 143, 64, 2, 344], ![-162, 84, 46, 8, 133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-67, -73, 90, 101, -286]] ![![3, 15, 20, 11, -74]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![567, 24, -170, -114, 446]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![567, 24, -170, -114, 446]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![16, 26, 16, 1, 0], ![22, 1, 30, 0, 1]] where
  M :=![![![567, 24, -170, -114, 446], ![228, 7, -70, -46, 178], ![92, 4, -27, -18, 62], ![36, 12, 6, 1, -14], ![96, 10, -22, -16, 57]]]
  hmulB := by decide  
  f := ![![![-1, 4, -2, 2, -2]], ![![-4, 3, -6, -10, 26]], ![![20, -40, 21, 18, -50]], ![![4, -10, 2, 1, -2]], ![![14, -27, 14, 14, -37]]]
  g := ![![![-181, 62, -286, -114, 446], ![-72, 25, -114, -46, 178], ![-24, 10, -39, -18, 62], ![8, 0, 10, 1, -14], ![-22, 9, -36, -16, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [35, 12, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 13, 3], [11, 27, 38], [0, 1]]
 g := ![![[32, 20, 25], [27, 33], [11, 25], [33, 39, 1], []], ![[27, 29, 19, 28], [7, 18], [9, 37], [19, 37, 18, 14], [19, 9]], ![[10, 30, 15, 14], [19, 21], [17, 37], [5, 16, 40, 26], [25, 9]]]
 h' := ![![[28, 13, 3], [21, 34, 36], [33, 31, 22], [34, 2, 5], [0, 0, 1], [0, 1]], ![[11, 27, 38], [9, 9, 8], [34, 4, 31], [29, 8, 18], [37, 21, 27], [28, 13, 3]], ![[0, 1], [24, 39, 38], [22, 6, 29], [17, 31, 18], [25, 20, 13], [11, 27, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 27], []]
 b := ![[], [11, 26, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [35, 12, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4834473, 5805429, -4578626, -4107524, 20619603]
  a := ![-26, 23, -80, -56, 235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9579155, 2243450, -13596252, -4107524, 20619603]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -3, -1, 0, -2]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-3, -3, -1, 0, -2]] 
 ![![41, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![22, 0, 0, 0, 1]] where
  M :=![![![-3, -3, -1, 0, -2], ![0, -1, 1, 1, -10], ![-2, 11, 12, 6, -32], ![-12, 36, 33, 14, -52], ![-6, 17, 16, 7, -27]]]
  hmulB := by decide  
  f := ![![![-29, 38, -25, -23, 62]], ![![-1, 0, 0, -1, 2]], ![![-24, 34, -22, -17, 48]], ![![-21, 25, -18, -22, 56]], ![![-16, 21, -14, -13, 35]]]
  g := ![![![2, -3, -1, 0, -2], ![4, -1, 1, 1, -10], ![3, 11, 12, 6, -32], ![-10, 36, 33, 14, -52], ![-4, 17, 16, 7, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -18, -9, -1, -36]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![15, -18, -9, -1, -36]] 
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![15, -18, -9, -1, -36], ![2, 50, 61, 32, -198], ![-64, 232, 222, 99, -414], ![-198, 449, 367, 141, -288], ![-94, 223, 186, 73, -173]]]
  hmulB := by decide  
  f := ![![![245, -101, 3, -52, 144]], ![![134, -53, 1, -25, 72]], ![![42, -9, -8, -20, 54]], ![![193, -113, 30, -22, 54]], ![![26, -13, 2, -5, 13]]]
  g := ![![![16, -18, -9, -1, -36], ![-42, 50, 61, 32, -198], ![-199, 232, 222, 99, -414], ![-389, 449, 367, 141, -288], ![-193, 223, 186, 73, -173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![567, 24, -170, -114, 446]] ![![-3, -3, -1, 0, -2]]
  ![![-2669, -117, 791, 530, -2048]] where
 M := ![![![-2669, -117, 791, 530, -2048]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-2669, -117, 791, 530, -2048]] ![![15, -18, -9, -1, -36]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-3321, 6970, 6068, 2460, -6560]]]
 hmul := by decide  
 g := ![![![![-81, 170, 148, 60, -160]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -8, -6, -2, -4]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![5, -8, -6, -2, -4]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![36, 40, 1, 0, 0], ![22, 27, 0, 1, 0], ![9, 36, 0, 0, 1]] where
  M :=![![![5, -8, -6, -2, -4], ![4, 7, 14, 8, -56], ![-16, 68, 63, 30, -136], ![-60, 150, 130, 49, -140], ![-28, 74, 64, 26, -79]]]
  hmulB := by decide  
  f := ![![![1063, 52, -318, -214, 836]], ![![428, 13, -122, -84, 328]], ![![1292, 56, -381, -258, 1008]], ![![814, 35, -240, -163, 636]], ![![585, 22, -170, -116, 453]]]
  g := ![![![7, 10, -6, -2, -4], ![-4, 29, 14, 8, -56], ![-40, 38, 63, 30, -136], ![-106, -31, 130, 49, -140], ![-51, -8, 64, 26, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 42], [0, 1]]
 g := ![![[32, 24], [27, 14], [16], [31, 24], [1]], ![[40, 19], [3, 29], [16], [39, 19], [1]]]
 h' := ![![[29, 42], [7, 14], [34, 33], [16, 4], [13, 29], [0, 1]], ![[0, 1], [26, 29], [2, 10], [3, 39], [37, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [10, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1779, -983, 5804, 4911, -15286]
  a := ![11, -6, 39, 29, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4131, 4292, 5804, 4911, -15286]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, -2, -1, 2]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![5, -1, -2, -1, 2]] 
 ![![43, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![5, -1, -2, -1, 2], ![2, 2, 2, 1, -8], ![-2, 11, 11, 5, -22], ![-10, 25, 20, 8, -20], ![-4, 12, 10, 4, -11]]]
  hmulB := by decide  
  f := ![![![19, -29, 16, -3, -2]], ![![5, -7, 4, 0, -2]], ![![2, -3, 1, -3, 6]], ![![23, -38, 22, 1, -14]], ![![7, -11, 6, -1, -1]]]
  g := ![![![1, -1, -2, -1, 2], ![1, 2, 2, 1, -8], ![-2, 11, 11, 5, -22], ![-11, 25, 20, 8, -20], ![-5, 12, 10, 4, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -1, 3, 2, -8]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-11, -1, 3, 2, -8]] 
 ![![43, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![28, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-11, -1, 3, 2, -8], ![-4, -1, 1, 1, -4], ![-2, 1, 0, 0, -2], ![0, 0, 5, 2, -10], ![-2, 1, 2, 1, -5]]]
  hmulB := by decide  
  f := ![![![-7, 8, -3, 1, 4]], ![![-2, 2, -1, 0, 2]], ![![-4, 4, -2, 1, 2]], ![![-2, 3, -3, -1, 4]], ![![-1, 1, -1, 0, 1]]]
  g := ![![![-1, -1, 3, 2, -8], ![0, -1, 1, 1, -4], ![0, 1, 0, 0, -2], ![-2, 0, 5, 2, -10], ![-1, 1, 2, 1, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2

def I43N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -5, -1, 2, 0]] i)))

def SI43N3: IdealEqSpanCertificate' Table ![![23, -5, -1, 2, 0]] 
 ![![43, 0, 0, 0, 0], ![23, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![23, -5, -1, 2, 0], ![-4, 25, -19, -11, 36], ![22, -51, 30, 0, -18], ![0, 40, -15, 48, -90], ![6, -3, 2, 5, -11]]]
  hmulB := by decide  
  f := ![![![123, -246, -191, -69, 72]], ![![69, -132, -100, -35, 18]], ![![82, -146, -106, -35, -18]], ![![91, -157, -112, -36, -36]], ![![71, -129, -95, -32, -5]]]
  g := ![![![2, -5, -1, 2, 0], ![-14, 25, -19, -11, 36], ![19, -51, 30, 0, -18], ![4, 40, -15, 48, -90], ![3, -3, 2, 5, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N3 : Nat.card (O ⧸ I43N3) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N3)

lemma isPrimeI43N3 : Ideal.IsPrime I43N3 := prime_ideal_of_norm_prime hp43.out _ NI43N3
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![5, -8, -6, -2, -4]] ![![5, -1, -2, -1, 2]]
  ![![57, -185, -172, -75, 290]] where
 M := ![![![57, -185, -172, -75, 290]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![57, -185, -172, -75, 290]] ![![-11, -1, 3, 2, -8]]
  ![![-123, 246, 191, 69, -72]] where
 M := ![![![-123, 246, 191, 69, -72]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N2 : IdealMulLeCertificate' Table 
  ![![-123, 246, 191, 69, -72]] ![![23, -5, -1, 2, 0]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2, I43N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
    exact isPrimeI43N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1 ⊙ MulI43N2)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![125, 2, -40, -26, 102]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![125, 2, -40, -26, 102]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![6, 35, 7, 1, 0], ![41, 20, 6, 0, 1]] where
  M :=![![![125, 2, -40, -26, 102], ![52, -3, -20, -12, 42], ![24, -2, -3, -2, -6], ![4, 28, 24, 13, -66], ![20, 12, 6, 2, -17]]]
  hmulB := by decide  
  f := ![![![3, -6, 4, 2, -6]], ![![-4, 11, -8, 0, 6]], ![![0, -10, -1, -14, 30]], ![![-2, 5, -5, -1, 6]], ![![1, -2, 0, 0, 1]]]
  g := ![![![-83, -24, -10, -26, 102], ![-34, -9, -4, -12, 42], ![6, 4, 1, -2, -6], ![56, 19, 7, 13, -66], ![15, 6, 2, 2, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [19, 20, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 39, 43], [37, 7, 4], [0, 1]]
 g := ![![[46, 37, 7], [40, 43, 12], [7, 20, 18], [14, 9, 1], []], ![[28, 2, 36, 19], [27, 19, 46, 41], [26, 29, 11, 46], [1, 33, 7, 39], [20, 16]], ![[40, 28, 26, 18], [34, 24, 26, 27], [42, 4, 3, 16], [32, 40, 45, 21], [12, 16]]]
 h' := ![![[19, 39, 43], [39, 45, 30], [8, 18, 23], [16, 19, 21], [0, 0, 1], [0, 1]], ![[37, 7, 4], [42, 44, 30], [7, 31, 42], [25, 18, 24], [28, 26, 7], [19, 39, 43]], ![[0, 1], [26, 5, 34], [33, 45, 29], [5, 10, 2], [13, 21, 39], [37, 7, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 41], []]
 b := ![[], [3, 35, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [19, 20, 38, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![410435, -1046488, 517896, 102600, -478944]
  a := ![-4, 2, -12, -20, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![413437, 105136, 56880, 102600, -478944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 6, -4, -2, 6]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-3, 6, -4, -2, 6]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![14, 40, 1, 0, 0], ![4, 12, 0, 1, 0], ![18, 16, 0, 0, 1]] where
  M :=![![![-3, 6, -4, -2, 6], ![4, -11, 8, 0, -6], ![0, 10, 1, 14, -30], ![-28, 44, -28, -39, 102], ![-4, 8, -2, -2, 7]]]
  hmulB := by decide  
  f := ![![![-125, -2, 40, 26, -102]], ![![-52, 3, 20, 12, -42]], ![![-82, 2, 29, 18, -66]], ![![-24, 0, 8, 5, -18]], ![![-66, 0, 22, 14, -53]]]
  g := ![![![-1, 2, -4, -2, 6], ![0, -5, 8, 0, -6], ![10, 6, 1, 14, -30], ![-28, 0, -28, -39, 102], ![-2, 0, -2, -2, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P1 : CertificateIrreducibleZModOfList' 47 2 2 5 [14, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 46], [0, 1]]
 g := ![![[32, 37], [37, 9], [2, 17], [21, 14], [1]], ![[0, 10], [0, 38], [0, 30], [0, 33], [1]]]
 h' := ![![[22, 46], [46, 15], [19, 44], [35, 39], [33, 22], [0, 1]], ![[0, 1], [0, 32], [0, 3], [0, 8], [0, 25], [22, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [42, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N1 : CertifiedPrimeIdeal' SI47N1 47 where
  n := 2
  hpos := by decide
  P := [14, 25, 1]
  hirr := P47P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2602, -5037, -4550, -1687, 2664]
  a := ![-4, 8, -7, -3, 49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![534, 3289, -4550, -1687, 2664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N1 B_one_repr
lemma NI47N1 : Nat.card (O ⧸ I47N1) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![125, 2, -40, -26, 102]] ![![-3, 6, -4, -2, 6]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![571, -7, -147, -114, 430]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![571, -7, -147, -114, 430]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![51, 43, 2, 34, 1]] where
  M :=![![![571, -7, -147, -114, 430], ![228, 27, -69, -7, 98], ![14, 123, -120, -132, 364], ![264, -482, 319, 176, -556], ![110, -33, -4, -15, 51]]]
  hmulB := by decide  
  f := ![![![-7, 16, 13, 5, -10]], ![![-10, 8, 1, -2, 40]], ![![4, -52, -58, -29, 164]], ![![58, -189, -177, -77, 298]], ![![23, -103, -104, -48, 223]]]
  g := ![![![-403, -349, -19, -278, 430], ![-90, -79, -5, -63, 98], ![-350, -293, -16, -236, 364], ![540, 442, 27, 360, -556], ![-47, -42, -2, -33, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [19, 49, 26, 33, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 39, 31, 38], [52, 23, 24, 22], [19, 43, 51, 46], [0, 1]]
 g := ![![[25, 11, 29, 16], [23, 27, 44], [44, 19, 50, 17], [3, 20, 1], []], ![[27, 6, 41, 36, 5, 15], [0, 13, 1], [43, 10, 39, 14, 1, 10], [47, 48, 40], [49, 14, 43, 50, 12, 17]], ![[21, 48, 47, 37, 41, 21], [9, 30, 1], [19, 8, 45, 46, 28, 48], [3, 10, 15], [14, 14, 37, 16, 33, 48]], ![[29, 37, 10, 22, 21, 52], [29, 16, 6], [32, 36, 4, 9, 25, 4], [4, 10, 24], [9, 34, 39, 17, 1, 28]]]
 h' := ![![[2, 39, 31, 38], [25, 28, 10, 4], [12, 43, 25, 37], [49, 3, 36, 21], [0, 0, 0, 1], [0, 1]], ![[52, 23, 24, 22], [16, 49, 52, 23], [4, 37, 30, 52], [15, 49, 15, 32], [31, 27, 43, 27], [2, 39, 31, 38]], ![[19, 43, 51, 46], [35, 13, 31, 38], [10, 30, 48, 52], [0, 15, 35, 22], [51, 18, 18, 42], [52, 23, 24, 22]], ![[0, 1], [33, 16, 13, 41], [1, 49, 3, 18], [24, 39, 20, 31], [10, 8, 45, 36], [19, 43, 51, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [38, 39, 47], []]
 b := ![[], [], [32, 21, 40, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [19, 49, 26, 33, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1041167, -2642352, -2436286, -952687, 2729509]
  a := ![2, -3, 6, 2, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2606864, -2264363, -148968, -1768981, 2729509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 16, 13, 5, -10]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-7, 16, 13, 5, -10]] 
 ![![53, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-7, 16, 13, 5, -10], ![-10, 8, 1, -2, 40], ![4, -52, -58, -29, 164], ![58, -189, -177, -77, 298], ![26, -89, -84, -37, 149]]]
  hmulB := by decide  
  f := ![![![571, -7, -147, -114, 430]], ![![209, -2, -54, -41, 156]], ![![108, 1, -30, -24, 88]], ![![242, -12, -55, -44, 168]], ![![196, -3, -50, -39, 147]]]
  g := ![![![-7, 16, 13, 5, -10], ![-16, 8, 1, -2, 40], ![-14, -52, -58, -29, 164], ![33, -189, -177, -77, 298], ![13, -89, -84, -37, 149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![571, -7, -147, -114, 430]] ![![-7, 16, 13, 5, -10]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 138, 127, 55, -210]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-41, 138, 127, 55, -210]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![19, 12, 33, 1, 0], ![49, 48, 44, 0, 1]] where
  M :=![![![-41, 138, 127, 55, -210], ![-110, 224, 173, 62, -60], ![-124, 12, -90, -77, 816], ![154, -1017, -1081, -521, 2694], ![54, -445, -484, -237, 1273]]]
  hmulB := by decide  
  f := ![![![23, -3, -7, -16, 42]], ![![32, -35, 25, 31, -78]], ![![-62, 141, -96, -52, 168]], ![![-19, 66, -48, -28, 90]], ![![-1, 74, -57, -27, 97]]]
  g := ![![![156, 162, 128, 55, -210], ![28, 40, 13, 62, -60], ![-655, -648, -567, -77, 816], ![-2067, -2103, -1736, -521, 2694], ![-980, -995, -825, -237, 1273]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [49, 52, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 20, 35], [30, 38, 24], [0, 1]]
 g := ![![[38, 0, 1], [42, 2, 45], [34, 21], [23, 49, 9], [1]], ![[1, 44, 52, 22], [14, 10, 55, 25], [26, 49], [25, 12, 25, 15], [34, 11, 40, 41]], ![[42, 0, 30, 39], [17, 41, 16, 34], [33, 46], [20, 27, 10, 40], [9, 50, 2, 18]]]
 h' := ![![[26, 20, 35], [7, 31, 1], [22, 50, 35], [53, 43, 32], [10, 7, 56], [0, 1]], ![[30, 38, 24], [38, 50, 2], [39, 48, 12], [30, 25, 7], [39, 21, 13], [26, 20, 35]], ![[0, 1], [24, 37, 56], [11, 20, 12], [34, 50, 20], [9, 31, 49], [30, 38, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 11], []]
 b := ![[], [24, 40, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [49, 52, 3, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73849, -153865, 121390, 60979, -208284]
  a := ![-3, 3, -2, -10, 30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![154596, 154441, 123281, 60979, -208284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -34, 25, 13, -44]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![7, -34, 25, 13, -44]] 
 ![![59, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![7, -34, 25, 13, -44], ![-26, 64, -37, 4, 14], ![-8, -36, 8, -71, 142], ![142, -221, 177, 221, -568], ![14, -31, 22, 15, -45]]]
  hmulB := by decide  
  f := ![![![-297, 597, 467, 170, -196]], ![![-41, 72, 52, 17, 12]], ![![-44, 57, 32, 6, 86]], ![![-196, 350, 257, 86, 26]], ![![-85, 148, 107, 35, 25]]]
  g := ![![![5, -34, 25, 13, -44], ![-10, 64, -37, 4, 14], ![10, -36, 8, -71, 142], ![21, -221, 177, 221, -568], ![4, -31, 22, 15, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 2, 1, -4]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![-3, 1, 2, 1, -4]] 
 ![![59, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![50, 0, 0, 0, 1]] where
  M :=![![![-3, 1, 2, 1, -4], ![-2, 2, 2, 1, -2], ![-2, 1, -1, -1, 8], ![2, -11, -8, -4, 22], ![0, -4, -4, -2, 11]]]
  hmulB := by decide  
  f := ![![![-21, 9, 0, 7, -20]], ![![-7, 3, 0, 2, -6]], ![![-18, 7, 1, 7, -20]], ![![-7, 6, -2, 1, -2]], ![![-18, 8, 0, 6, -17]]]
  g := ![![![1, 1, 2, 1, -4], ![-1, 2, 2, 1, -2], ![-6, 1, -1, -1, 8], ![-7, -11, -8, -4, 22], ![-4, -4, -4, -2, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-41, 138, 127, 55, -210]] ![![7, -34, 25, 13, -44]]
  ![![-21, 9, 0, 7, -20]] where
 M := ![![![-21, 9, 0, 7, -20]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-21, 9, 0, 7, -20]] ![![-3, 1, 2, 1, -4]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [44, 60, 14, 30, 39, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 59, 28, 18, 12], [50, 38, 40, 52, 26], [2, 19, 12, 56, 59], [19, 5, 42, 57, 25], [0, 1]]
 g := ![![[33, 15, 10, 13, 14], [36, 39, 57, 47], [6, 41, 17, 2, 56], [27, 22, 1], []], ![[44, 44, 3, 12, 25, 29, 31, 19], [2, 16, 56, 1], [38, 57, 25, 30, 53, 3, 50, 4], [42, 21, 49, 4, 40, 42, 15, 27], [4, 52, 39, 59, 7, 50, 42, 20]], ![[50, 2, 22, 9, 54, 18, 14, 50], [44, 48, 3, 1], [60, 12, 44, 24, 33, 41, 55, 28], [26, 34, 40, 3, 21, 27, 19, 38], [24, 29, 29, 58, 31, 16, 41, 8]], ![[23, 38, 7, 55, 33, 9, 17, 29], [31, 4, 28, 42], [40, 21, 23, 7, 0, 37, 35, 23], [47, 21, 35, 28, 10, 25, 35, 59], [40, 17, 24, 51, 16, 44, 8, 53]], ![[31, 41, 31, 5, 16, 3, 2, 56], [38, 40, 52, 16], [14, 30, 11, 24, 40, 7, 14, 14], [39, 48, 31, 44, 49, 51, 41, 57], [48, 37, 30, 35, 29, 44, 18, 9]]]
 h' := ![![[12, 59, 28, 18, 12], [36, 0, 1, 38, 21], [41, 19, 46, 54, 48], [32, 35, 27, 42, 42], [0, 0, 0, 1], [0, 1]], ![[50, 38, 40, 52, 26], [47, 53, 2, 49, 24], [14, 3, 25, 17, 1], [7, 36, 15, 35, 38], [27, 24, 28, 26, 32], [12, 59, 28, 18, 12]], ![[2, 19, 12, 56, 59], [35, 34, 32, 16, 4], [18, 55, 60, 21, 1], [43, 32, 45, 57, 32], [53, 37, 55, 35, 10], [50, 38, 40, 52, 26]], ![[19, 5, 42, 57, 25], [34, 22, 5, 31, 57], [19, 6, 6, 23, 15], [35, 34, 35, 12, 18], [17, 8, 40, 21, 60], [2, 19, 12, 56, 59]], ![[0, 1], [40, 13, 21, 49, 16], [59, 39, 46, 7, 57], [34, 46, 0, 37, 53], [50, 53, 60, 39, 20], [19, 5, 42, 57, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 8, 39, 16], [], [], []]
 b := ![[], [30, 49, 13, 23, 19], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [44, 60, 14, 30, 39, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-636318206, 411137255, -1622480440, -1771641483, 4961228698]
  a := ![-8, 5, -28, -20, 73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10431446, 6739955, -26598040, -29043303, 81331618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB175I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB175I1 : PrimesBelowBoundCertificateInterval O 23 61 175 where
  m := 9
  g := ![1, 3, 2, 3, 4, 2, 2, 3, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB175I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2, I43N3]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
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
    · exact ![20511149]
    · exact ![29791, 31, 31]
    · exact ![1874161, 37]
    · exact ![68921, 41, 41]
    · exact ![1849, 43, 43, 43]
    · exact ![103823, 2209]
    · exact ![7890481, 53]
    · exact ![205379, 59, 59]
    · exact ![844596301]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
      exact NI43N3
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
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I31N1, I31N2, I37N1, I41N1, I41N2, I43N1, I43N2, I43N3, I53N1, I59N1, I59N2]
  Il := ![[], [I31N1, I31N2], [I37N1], [I41N1, I41N2], [I43N1, I43N2, I43N3], [], [I53N1], [I59N1, I59N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
