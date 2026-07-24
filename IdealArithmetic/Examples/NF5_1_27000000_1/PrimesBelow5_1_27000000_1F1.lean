
import IdealArithmetic.Examples.NF5_1_27000000_1.RI5_1_27000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2083, -208, 721, 349, 543]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-2083, -208, 721, 349, 543]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![3, 26, 15, 18, 1]] where
  M :=![![![-2083, -208, 721, 349, 543], ![-4344, -2268, -28, 7, 698], ![-620, -2193, -1563, -733, -342], ![3540, -321, -1788, -858, -1082], ![1134, -3048, -3030, -1432, -1043]]]
  hmulB := by decide  
  f := ![![![15, -6, 11, 5, -5]], ![![40, 10, -32, 27, 10]], ![![-60, -23, 9, -69, 22]], ![![-108, 27, 84, 8, -74]], ![![-53, 13, 28, -2, -26]]]
  g := ![![![-128, -494, -256, -325, 543], ![-222, -704, -362, -433, 698], ![14, 231, 123, 187, -342], ![234, 959, 498, 642, -1082], ![147, 830, 435, 598, -1043]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [17, 3, 8, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 5, 19, 24], [1, 7, 28, 16], [13, 16, 11, 18], [0, 1]]
 g := ![![[13, 4, 11, 28], [6, 16, 1], [26, 8, 25, 1], []], ![[4, 7, 16, 28, 13, 7], [6, 18, 23], [20, 0, 4, 6, 4, 23], [25, 22, 26, 5, 11, 20]], ![[16, 9, 1, 1, 5, 1], [6, 16, 1], [4, 2, 7, 15, 17, 9], [6, 11, 16, 26, 16, 7]], ![[8, 25, 26, 20, 26, 18], [6, 18, 23], [19, 2, 26, 6, 24, 17], [20, 28, 27, 19, 8, 3]]]
 h' := ![![[11, 5, 19, 24], [5, 9, 13, 17], [22, 18, 10, 1], [0, 0, 0, 1], [0, 1]], ![[1, 7, 28, 16], [1, 10, 16, 4], [25, 9, 19, 9], [7, 3, 25, 23], [11, 5, 19, 24]], ![[13, 16, 11, 18], [13, 3, 0, 7], [12, 11, 19, 28], [15, 19, 23, 8], [1, 7, 28, 16]], ![[0, 1], [8, 7, 0, 1], [9, 20, 10, 20], [1, 7, 10, 26], [13, 16, 11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [25, 19, 18], []]
 b := ![[], [], [11, 0, 28, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [17, 3, 8, 4, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-172927579, 62963204, 277765427, 112056557, -250624747]
  a := ![0, 8, 5, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19963678, 226869194, 139211608, 159424207, -250624747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -6, 11, 5, -5]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![15, -6, 11, 5, -5]] 
 ![![29, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![15, -6, 11, 5, -5], ![40, 10, -32, 27, 10], ![-60, -23, 9, -69, 22], ![-108, 27, 84, 8, -74], ![222, -6, -36, 116, 3]]]
  hmulB := by decide  
  f := ![![![-2083, -208, 721, 349, 543]], ![![-1730, -236, 546, 265, 436]], ![![-596, -133, 145, 71, 138]], ![![-1099, -133, 361, 175, 281]], ![![-751, -184, 169, 83, 170]]]
  g := ![![![1, -6, 11, 5, -5], ![-17, 10, -32, 27, 10], ![45, -23, 9, -69, 22], ![-24, 27, 84, 8, -74], ![-47, -6, -36, 116, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-2083, -208, 721, 349, 543]] ![![15, -6, 11, 5, -5]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 149, -64, 153, -76]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-73, 149, -64, 153, -76]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![3, 27, 9, 9, 1]] where
  M :=![![![-73, 149, -64, 153, -76], ![608, -294, -160, -129, 306], ![-1528, 353, 221, -337, -282], ![824, 7, 488, 736, -490], ![1452, -14, -914, 512, 515]]]
  hmulB := by decide  
  f := ![![![-383, 81, 232, 111, 128]], ![![-1024, -292, 196, 97, 222]], ![![-376, -511, -265, -123, -14]], ![![568, -307, -500, -238, -234]], ![![-879, -511, -49, -19, 129]]]
  g := ![![![5, 71, 20, 27, -76], ![-10, -276, -94, -93, 306], ![-22, 257, 89, 71, -282], ![74, 427, 158, 166, -490], ![-3, -449, -179, -133, 515]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 4 2 4 [23, 11, 20, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 14, 24, 14], [4, 16, 27, 24], [3, 0, 11, 24], [0, 1]]
 g := ![![[13, 6, 15, 28], [16, 26, 8, 20], [17, 25, 18, 1], []], ![[1, 1, 28, 0, 28, 9], [27, 9, 8, 19, 13, 5], [9, 25, 20, 7, 17, 10], [10, 28, 9, 28, 16, 16]], ![[11, 4, 12, 29, 28, 6], [20, 15, 3, 16, 30, 13], [16, 24, 14, 28, 25, 12], [24, 6, 28, 0, 27, 29]], ![[18, 3, 15, 21, 9, 24], [18, 12, 19, 20, 29, 15], [2, 30, 9, 3, 7, 6], [10, 16, 21, 10, 0, 29]]]
 h' := ![![[11, 14, 24, 14], [4, 21, 18, 20], [12, 13, 25, 19], [0, 0, 0, 1], [0, 1]], ![[4, 16, 27, 24], [26, 14, 11, 26], [5, 19, 3, 10], [16, 19, 19, 18], [11, 14, 24, 14]], ![[3, 0, 11, 24], [23, 18, 2, 15], [12, 5, 20, 21], [8, 25, 16, 27], [4, 16, 27, 24]], ![[0, 1], [13, 9, 0, 1], [15, 25, 14, 12], [14, 18, 27, 16], [3, 0, 11, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 10, 9], []]
 b := ![[], [], [24, 1, 25, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 4
  hpos := by decide
  P := [23, 11, 20, 13, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3641482516, 1018576995, 2792091595, 4993773967, -3386544264]
  a := ![3, -5, -3, -1, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![445197268, 2982428133, 1073257741, 1144279753, -3386544264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 923521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![383, -81, -232, -111, -128]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![383, -81, -232, -111, -128]] 
 ![![31, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![383, -81, -232, -111, -128], ![1024, 292, -196, -97, -222], ![376, 511, 265, 123, 14], ![-568, 307, 500, 238, 234], ![180, 838, 622, 292, 147]]]
  hmulB := by decide  
  f := ![![![73, -149, 64, -153, 76]], ![![11, -53, 32, -60, 22]], ![![54, -21, -3, 1, 14]], ![![37, -130, 40, -157, 82]], ![![-28, -38, 46, -56, 3]]]
  g := ![![![191, -81, -232, -111, -128], ![65, 292, -196, -97, -222], ![-330, 511, 265, 123, 14], ![-447, 307, 500, 238, 234], ![-678, 838, 622, 292, 147]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-73, 149, -64, 153, -76]] ![![383, -81, -232, -111, -128]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-31, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)
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


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [3, 21, 18, 22, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 1, 13, 1, 9], [33, 31, 21, 36, 24], [18, 28, 26, 26, 36], [27, 13, 14, 11, 5], [0, 1]]
 g := ![![[28, 26, 31, 25, 30], [9, 30, 2, 10], [6, 30, 14, 31, 1], [], []], ![[33, 12, 11, 34, 35, 6, 10, 12], [2, 10, 7, 21], [3, 5, 24, 1, 1, 8, 8, 28], [29, 24, 7, 26], [21, 3, 13, 7]], ![[24, 23, 30, 16, 7, 22, 6, 13], [5, 15, 13, 4], [6, 14, 8, 1, 12, 0, 23, 19], [36, 16, 10, 36], [12, 0, 11, 21]], ![[20, 21, 25, 32, 31, 25, 17, 3], [5, 26, 12, 10], [8, 34, 13, 15, 30, 7, 1, 33], [6, 7, 35, 3], [36, 25, 16, 1]], ![[7, 23, 26, 13, 31, 16, 21, 24], [34, 20, 11, 12], [13, 33, 8, 2, 11, 32, 4, 13], [10, 36, 3, 10], [15, 25, 34, 25]]]
 h' := ![![[27, 1, 13, 1, 9], [1, 23, 12, 19, 20], [19, 6, 34, 14, 26], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[33, 31, 21, 36, 24], [3, 14, 34, 11, 10], [3, 2, 31, 35, 13], [24, 22, 36, 22, 31], [0, 11, 1, 10, 10], [27, 1, 13, 1, 9]], ![[18, 28, 26, 26, 36], [12, 36, 28, 15, 31], [29, 30, 36, 0, 2], [33, 30, 9, 20, 29], [17, 18, 26, 12, 31], [33, 31, 21, 36, 24]], ![[27, 13, 14, 11, 5], [23, 24, 7, 7, 21], [36, 26, 17, 27, 26], [18, 23, 6, 4, 2], [31, 29, 18, 34, 22], [18, 28, 26, 26, 36]], ![[0, 1], [34, 14, 30, 22, 29], [32, 10, 30, 35, 7], [35, 36, 23, 28, 11], [18, 16, 28, 18, 11], [27, 13, 14, 11, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 17, 23, 11], [], [], []]
 b := ![[], [36, 21, 10, 14, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [3, 21, 18, 22, 6, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4564099961, -287346292, -73623488, -3331620156, 933610492]
  a := ![1, 3, 2, -1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-123354053, -7766116, -1989824, -90043788, 25232716]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181, -134, -33, -17, 15]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-181, -134, -33, -17, 15]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![18, 2, 6, 18, 1]] where
  M :=![![![-181, -134, -33, -17, 15], ![-120, -314, -204, -79, -34], ![196, -83, -167, -91, -62], ![308, 221, 48, -20, -74], ![526, 22, -180, -48, -153]]]
  hmulB := by decide  
  f := ![![![2373, -1436, 633, -413, 495]], ![![-3960, 2396, -1056, 689, -826]], ![![5284, -3197, 1409, -919, 1102]], ![![-2428, 1469, -648, 422, -506]], ![![608, -368, 162, -106, 127]]]
  g := ![![![-11, -4, -3, -7, 15], ![12, -6, 0, 13, -34], ![32, 1, 5, 25, -62], ![40, 9, 12, 32, -74], ![80, 8, 18, 66, -153]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [16, 27, 0, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 8, 35, 33], [2, 21, 34, 1], [19, 11, 13, 7], [0, 1]]
 g := ![![[19, 3, 40, 36], [7, 32, 40], [25, 37, 10], [4, 1], []], ![[35, 18, 23, 35, 1, 5], [40, 10, 33], [7, 34, 16], [33, 10, 15, 25, 11, 23], [4, 24, 23]], ![[36, 23, 33, 28, 34, 36], [25, 29, 33], [5, 15, 31], [29, 9, 11, 5, 2, 18], [10, 31, 1]], ![[13, 11, 24, 13, 34, 11], [27, 0, 40], [32], [25, 29, 1, 9, 35, 34], [31, 9, 8]]]
 h' := ![![[24, 8, 35, 33], [6, 22, 36, 35], [6, 9, 2, 9], [18, 40, 14, 16], [0, 0, 1], [0, 1]], ![[2, 21, 34, 1], [15, 3, 37, 36], [9, 3, 14, 22], [11, 26, 27, 4], [20, 15, 31, 22], [24, 8, 35, 33]], ![[19, 11, 13, 7], [20, 19, 5, 6], [25, 33, 7, 19], [33, 36, 14, 21], [8, 15, 11, 10], [2, 21, 34, 1]], ![[0, 1], [11, 38, 4, 5], [22, 37, 18, 32], [40, 21, 27], [29, 11, 39, 9], [19, 11, 13, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [32, 29, 40], []]
 b := ![[], [], [11, 5, 15, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [16, 27, 0, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-363382369, 857764136, 3238993828, 2476877707, -3193787486]
  a := ![1, -11, -7, -1, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1393287619, 176715588, 546383384, 1462562255, -3193787486]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2373, -1436, 633, -413, 495]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![2373, -1436, 633, -413, 495]] 
 ![![41, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![2373, -1436, 633, -413, 495], ![-3960, 2396, -1056, 689, -826], ![5284, -3197, 1409, -919, 1102], ![-2428, 1469, -648, 422, -506], ![2134, -1292, 570, -372, 445]]]
  hmulB := by decide  
  f := ![![![-181, -134, -33, -17, 15]], ![![-25, -24, -9, -4, 1]], ![![-110, -87, -25, -13, 8]], ![![-147, -109, -27, -15, 11]], ![![4, -6, -6, -2, -3]]]
  g := ![![![160, -1436, 633, -413, 495], ![-267, 2396, -1056, 689, -826], ![356, -3197, 1409, -919, 1102], ![-163, 1469, -648, 422, -506], ![144, -1292, 570, -372, 445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-181, -134, -33, -17, 15]] ![![2373, -1436, 633, -413, 495]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-795, -44, 54, -528, 68]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-795, -44, 54, -528, 68]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![37, 12, 40, 15, 1]] where
  M :=![![![-795, -44, 54, -528, 68], ![-544, 271, 1104, 500, -1056], ![4496, -220, -1837, 1660, 1028], ![-3840, -576, -1404, -3945, 2188], ![-6720, 798, 4122, -1432, -2879]]]
  hmulB := by decide  
  f := ![![![-648401, 392348, -172950, 112824, -135236]], ![![1081888, -654651, 288576, -188252, 225648]], ![![-1443536, 873484, -385039, 251180, -301076]], ![![663360, -401400, 176940, -115427, 138356]], ![![-1380991, 835638, -368356, 240297, -288031]]]
  g := ![![![-77, -20, -62, -36, 68], ![896, 301, 1008, 380, -1056], ![-780, -292, -999, -320, 1028], ![-1972, -624, -2068, -855, 2188], ![2321, 822, 2774, 971, -2879]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 4 2 5 [12, 42, 1, 35, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 6, 14, 30], [24, 39, 33, 17], [2, 40, 39, 39], [0, 1]]
 g := ![![[23, 8, 4, 35], [22, 20, 32, 41], [16, 39, 13], [8, 1], []], ![[0, 11, 16, 22, 28, 39], [7, 27, 12, 17, 20, 19], [40, 29, 6], [14, 36, 4, 29, 21, 18], [35, 42, 40]], ![[41, 35, 32, 32, 42, 13], [40, 9, 31, 39, 13, 15], [4, 9, 6], [3, 20, 42, 27, 14, 35], [14, 37, 31]], ![[23, 9, 22, 37, 31, 30], [24, 12, 23, 13, 18, 30], [6, 8, 36], [6, 33, 34, 12, 5, 18], [14, 31, 16]]]
 h' := ![![[25, 6, 14, 30], [37, 33, 36, 32], [37, 15, 23, 16], [33, 39, 36, 20], [0, 0, 1], [0, 1]], ![[24, 39, 33, 17], [23, 15, 17, 13], [7, 35, 34, 38], [10, 15, 29, 36], [33, 3, 5, 11], [25, 6, 14, 30]], ![[2, 40, 39, 39], [24, 8, 29, 8], [35, 39, 28, 22], [13, 27, 12, 36], [21, 23, 4, 13], [24, 39, 33, 17]], ![[0, 1], [40, 30, 4, 33], [11, 40, 1, 10], [13, 5, 9, 37], [8, 17, 33, 19], [2, 40, 39, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 14, 41], []]
 b := ![[], [], [27, 24, 5, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 4
  hpos := by decide
  P := [12, 42, 1, 35, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![67761169, 142233023, 527200643, 494817798, -553513674]
  a := ![-1, 13, 9, 2, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![477855049, 157776677, 527156921, 204593556, -553513674]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 3418801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![648401, -392348, 172950, -112824, 135236]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![648401, -392348, 172950, -112824, 135236]] 
 ![![43, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![648401, -392348, 172950, -112824, 135236], ![-1081888, 654651, -288576, 188252, -225648], ![1443536, -873484, 385039, -251180, 301076], ![-663360, 401400, -176940, 115427, -138356], ![583392, -353010, 155610, -101512, 121677]]]
  hmulB := by decide  
  f := ![![![795, 44, -54, 528, -68]], ![![253, 7, -42, 148, 4]], ![![598, 44, -5, 428, -84]], ![![570, 40, 0, 411, -92]], ![![600, 6, -126, 328, 29]]]
  g := ![![![-26405, -392348, 172950, -112824, 135236], ![44059, 654651, -288576, 188252, -225648], ![-58786, -873484, 385039, -251180, 301076], ![27014, 401400, -176940, 115427, -138356], ![-23758, -353010, 155610, -101512, 121677]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-795, -44, 54, -528, 68]] ![![648401, -392348, 172950, -112824, 135236]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0, 0, 0]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]] where
  M :=![![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![0, 0, 0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 5 2 5 [1, 24, 23, 18, 30, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 37, 41, 44, 37], [39, 26, 32, 12, 18], [14, 24, 43, 3, 37], [4, 6, 25, 35, 2], [0, 1]]
 g := ![![[40, 44, 42, 20, 27], [17, 1, 35, 4, 6], [30, 46, 12, 24, 7], [1], []], ![[24, 3, 29, 36, 21, 34, 22, 36], [45, 44, 40, 40, 24, 12, 41, 2], [46, 37, 22, 27, 37, 10, 3, 42], [41, 26, 21, 45, 43, 5, 8, 37], [36, 2, 21, 6]], ![[5, 16, 20, 31, 6, 12, 46, 34], [24, 25, 35, 29, 9, 3, 24, 36], [41, 2, 39, 6, 24, 10, 0, 18], [7, 37, 19, 6, 39, 31, 28, 9], [38, 0, 18, 42]], ![[3, 27, 7, 23, 0, 15, 15, 36], [29, 29, 22, 1, 17, 2, 10, 42], [5, 28, 30, 22, 28, 32, 42, 24], [16, 19, 35, 45, 0, 11, 2, 21], [30, 37, 42, 6]], ![[24, 9, 7, 30, 13, 25, 0, 24], [26, 37, 17, 16, 13, 34, 17, 32], [9, 23, 10, 39, 40, 37, 40, 27], [36, 18, 15, 3, 13, 33, 19, 32], [15, 42, 20, 4]]]
 h' := ![![[7, 37, 41, 44, 37], [30, 21, 1, 42, 11], [17, 34, 28, 28, 10], [46, 23, 24, 29, 17], [0, 0, 1], [0, 1]], ![[39, 26, 32, 12, 18], [44, 45, 44, 14, 38], [10, 40, 2, 2, 13], [14, 46, 46, 38, 27], [13, 28, 12, 2, 46], [7, 37, 41, 44, 37]], ![[14, 24, 43, 3, 37], [11, 41, 42, 11, 13], [5, 33, 30, 36, 40], [37, 38, 19, 46, 1], [26, 35, 24, 32, 20], [39, 26, 32, 12, 18]], ![[4, 6, 25, 35, 2], [27, 35, 35, 36, 9], [45, 15, 20, 46, 27], [39, 29, 20, 1, 17], [25, 9, 19, 25, 24], [14, 24, 43, 3, 37]], ![[0, 1], [37, 46, 19, 38, 23], [45, 19, 14, 29, 4], [15, 5, 32, 27, 32], [1, 22, 38, 35, 4], [4, 6, 25, 35, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 23, 40, 32], [], [], []]
 b := ![[], [23, 4, 24, 37, 22], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 5
  hpos := by decide
  P := [1, 24, 23, 18, 30, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2075589983, -273053832, -548721804, -1955378224, 945505768]
  a := ![0, -10, -6, -10, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-44161489, -5809656, -11674932, -41603792, 20117144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 229345007 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![735, 532, 155, 63, -69]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![735, 532, 155, 63, -69]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![17, 33, 40, 6, 1]] where
  M :=![![![735, 532, 155, 63, -69], ![552, 1296, 800, 385, 126], ![-780, 291, 637, 289, 322], ![-1564, -863, -76, -22, 226], ![-1914, -74, 784, 372, 539]]]
  hmulB := by decide  
  f := ![![![-43, 2, 17, -17, -9]], ![![72, 10, 20, 69, -34]], ![![100, -23, -103, -15, 86]], ![![-380, -3, 68, -216, 2]], ![![63, -10, -49, 4, 38]]]
  g := ![![![36, 53, 55, 9, -69], ![-30, -54, -80, -7, 126], ![-118, -195, -231, -31, 322], ![-102, -157, -172, -26, 226], ![-209, -337, -392, -54, 539]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [46, 6, 15, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 4, 28, 25], [36, 52], [43, 49, 25, 28], [0, 1]]
 g := ![![[52, 17, 15, 1], [34, 19, 24], [6, 29, 41, 46], [28, 19, 1], []], ![[7, 33, 41, 4, 44, 11], [46, 51, 52], [28, 0, 33, 27, 5, 40], [39, 11, 25], [5, 41, 44, 22, 52, 43]], ![[33, 50, 17, 52], [22, 2, 24], [14, 14, 27, 7], [47, 15, 1], []], ![[11, 20, 36, 30, 10, 42], [3, 21, 52], [41, 46, 52, 41, 50, 13], [28, 44, 25], [10, 9, 40, 31, 1, 10]]]
 h' := ![![[46, 4, 28, 25], [41, 4, 51, 1], [42, 52, 30, 36], [37, 18, 3, 29], [0, 0, 0, 1], [0, 1]], ![[36, 52], [32, 24, 10, 44], [9, 41, 10, 30], [2, 48, 37, 37], [10, 50, 4, 48], [46, 4, 28, 25]], ![[43, 49, 25, 28], [47, 15, 0, 52], [30, 19, 49, 17], [2, 10, 8, 24], [16, 34, 2, 52], [36, 52]], ![[0, 1], [38, 10, 45, 9], [32, 47, 17, 23], [30, 30, 5, 16], [24, 22, 47, 5], [43, 49, 25, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [23], []]
 b := ![[], [], [31, 45, 15, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [46, 6, 15, 34, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142964960, 52399842, 185331220, 260790386, -223800986]
  a := ![13, 10, 7, 1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![74482674, 140336460, 172403220, 30256534, -223800986]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, 2, 17, -17, -9]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-43, 2, 17, -17, -9]] 
 ![![53, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-43, 2, 17, -17, -9], ![72, 10, 20, 69, -34], ![100, -23, -103, -15, 86], ![-380, -3, 68, -216, 2], ![-26, 44, 166, 120, -163]]]
  hmulB := by decide  
  f := ![![![735, 532, 155, 63, -69]], ![![579, 436, 135, 56, -51]], ![![540, 407, 129, 53, -46]], ![![442, 325, 98, 40, -40]], ![![477, 370, 123, 51, -38]]]
  g := ![![![2, 2, 17, -17, -9], ![-42, 10, 20, 69, -34], ![47, -23, -103, -15, 86], ![81, -3, 68, -216, 2], ![-123, 44, 166, 120, -163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![735, 532, 155, 63, -69]] ![![-43, 2, 17, -17, -9]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-881, 104, 465, 223, 275]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-881, 104, 465, 223, 275]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 35, 0, 1, 0], ![14, 34, 0, 0, 1]] where
  M :=![![![-881, 104, 465, 223, 275], ![-2200, -758, 312, 157, 446], ![-684, -1101, -625, -291, -66], ![1364, -535, -1032, -492, -514], ![-146, -1736, -1386, -652, -369]]]
  hmulB := by decide  
  f := ![![![-1221, 758, -327, 241, -271]], ![![2168, -1272, 492, -353, 482]], ![![-258, 157, -67, 47, -56]], ![![1308, -767, 300, -211, 288]], ![![948, -542, 198, -140, 211]]]
  g := ![![![-159, -289, 465, 223, 275], ![-196, -363, 312, 157, 446], ![110, 192, -625, -291, -66], ![320, 579, -1032, -492, -514], ![320, 570, -1386, -652, -369]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [36, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 58], [0, 1]]
 g := ![![[36, 41], [53, 3], [7], [48, 21], [2, 1]], ![[0, 18], [0, 56], [7], [31, 38], [4, 58]]]
 h' := ![![[2, 58], [39, 10], [37, 11], [42, 40], [46, 27], [0, 1]], ![[0, 1], [0, 49], [0, 48], [4, 19], [41, 32], [2, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [16, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [36, 57, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-906, -410, -301, -917, 715]
  a := ![-1, -5, -3, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-134, 125, -301, -917, 715]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![477, 14, -54, 296, -34]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![477, 14, -54, 296, -34]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![15, 45, 1, 0, 0], ![33, 41, 0, 1, 0], ![36, 56, 0, 0, 1]] where
  M :=![![![477, 14, -54, 296, -34], ![272, -155, -632, -336, 592], ![-2504, 156, 1089, -888, -632], ![2392, 336, 728, 2333, -1184], ![3700, -436, -2360, 688, 1701]]]
  hmulB := by decide  
  f := ![![![1541903, -933002, 411274, -268296, 321590]], ![![-2572720, 1556767, -686232, 447664, -536592]], ![![-1512053, 914955, -403317, 263104, -315370]], ![![-952139, 576151, -253970, 165677, -198590]], ![![-1477568, 894092, -394120, 257104, -308179]]]
  g := ![![![-123, -132, -54, 296, -34], ![-8, 151, -632, -336, 592], ![563, 389, 1089, -888, -632], ![-727, -1047, 728, 2333, -1184], ![-760, -300, -2360, 688, 1701]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [18, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 58], [0, 1]]
 g := ![![[12, 41], [56, 1], [51], [4, 17], [20, 1]], ![[6, 18], [17, 58], [51], [49, 42], [40, 58]]]
 h' := ![![[20, 58], [54, 10], [18, 1], [46, 46], [53, 28], [0, 1]], ![[0, 1], [18, 49], [38, 58], [22, 13], [23, 31], [20, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [31, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [18, 39, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13912, -2992, -1412, -12174, 3852]
  a := ![3, -14, -7, -4, 34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4582, 5830, -1412, -12174, 3852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 19, -6, -3, -10]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![51, 19, -6, -3, -10]] 
 ![![59, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![51, 19, -6, -3, -10], ![80, 70, 24, 11, -6], ![-16, 41, 41, 19, 14], ![-96, -21, 24, 12, 22], ![-72, 42, 66, 32, 31]]]
  hmulB := by decide  
  f := ![![![1721, -1037, 450, -297, 362]], ![![826, -498, 216, -143, 174]], ![![269, -162, 71, -46, 56]], ![![1635, -984, 426, -281, 344]], ![![229, -139, 60, -41, 49]]]
  g := ![![![-4, 19, -6, -3, -10], ![-47, 70, 24, 11, -6], ![-46, 41, 41, 19, 14], ![-8, -21, 24, 12, 22], ![-65, 42, 66, 32, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-881, 104, 465, 223, 275]] ![![477, 14, -54, 296, -34]]
  ![![-5393, -886, 1575, 819, 1385]] where
 M := ![![![-5393, -886, 1575, 819, 1385]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-5393, -886, 1575, 819, 1385]] ![![51, 19, -6, -3, -10]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-549467, -58941, 186735, 90506, 142249]]]
 hmul := by decide  
 g := ![![![![-9313, -999, 3165, 1534, 2411]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-281, 168, -74, 48, -58]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-281, 168, -74, 48, -58]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![2, 28, 43, 1, 0], ![37, 35, 60, 0, 1]] where
  M :=![![![-281, 168, -74, 48, -58], ![464, -283, 124, -80, 96], ![-616, 374, -169, 108, -128], ![280, -172, 76, -55, 60], ![-252, 152, -64, 44, -57]]]
  hmulB := by decide  
  f := ![![![-13, -4, 2, 0, 2]], ![![-16, -15, -4, 0, 0]], ![![8, -10, -13, -4, 0]], ![![-2, -14, -11, -3, 0]], ![![-9, -21, -14, -4, 1]]]
  g := ![![![29, 14, 22, 48, -58], ![-48, -23, -36, -80, 96], ![64, 30, 47, 108, -128], ![-30, -12, -19, -55, 60], ![29, 15, 24, 44, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [55, 4, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 45, 47], [60, 15, 14], [0, 1]]
 g := ![![[50, 20, 25], [42, 5], [48, 5, 19], [15, 15, 36], [1]], ![[28, 25, 48, 12], [56, 13], [52, 43, 32, 41], [38, 47, 33, 42], [27, 27, 41, 1]], ![[31, 16, 31, 27], [51, 14], [60, 45, 28, 9], [55, 0, 56, 13], [33, 13, 42, 60]]]
 h' := ![![[56, 45, 47], [53, 17, 5], [44, 8, 35], [29, 5, 18], [6, 57, 55], [0, 1]], ![[60, 15, 14], [30, 45, 20], [11, 17, 47], [32, 12, 17], [37, 13, 27], [56, 45, 47]], ![[0, 1], [53, 60, 36], [33, 36, 40], [12, 44, 26], [14, 52, 40], [60, 15, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4], []]
 b := ![[], [45, 52, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [55, 4, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-907980, 60438, 379549, -343706, -200121]
  a := ![1, -7, -5, -1, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![117769, 273581, 445347, -343706, -200121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-863, 522, -230, 150, -180]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-863, 522, -230, 150, -180]] 
 ![![61, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-863, 522, -230, 150, -180], ![1440, -871, 384, -250, 300], ![-1920, 1162, -513, 334, -400], ![880, -534, 236, -155, 184], ![-776, 470, -206, 136, -163]]]
  hmulB := by decide  
  f := ![![![-291, 46, 162, 74, 92]], ![![-55, 3, 26, 12, 16]], ![![-80, 6, 39, 18, 24]], ![![-65, 8, 34, 15, 20]], ![![-126, 10, 62, 28, 37]]]
  g := ![![![9, 522, -230, 150, -180], ![-15, -871, 384, -250, 300], ![20, 1162, -513, 334, -400], ![-9, -534, 236, -155, 184], ![8, 470, -206, 136, -163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99, -26, -64, -30, -34]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![99, -26, -64, -30, -34]] 
 ![![61, 0, 0, 0, 0], ![28, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![58, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![99, -26, -64, -30, -34], ![272, 69, -60, -30, -60], ![104, 136, 69, 30, 0], ![-136, 90, 136, 69, 60], ![68, 226, 158, 76, 39]]]
  hmulB := by decide  
  f := ![![![713751, -431890, 190380, -124194, 148866]], ![![308100, -186431, 82180, -53610, 64260]], ![![271767, -164446, 72489, -47288, 56682]], ![![666678, -403406, 177824, -116003, 139048]], ![![700877, -424100, 186946, -121954, 146181]]]
  g := ![![![97, -26, -64, -30, -34], ![80, 69, -60, -30, -60], ![-113, 136, 69, 30, 0], ![-214, 90, 136, 69, 60], ![-267, 226, 158, 76, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-281, 168, -74, 48, -58]] ![![-863, 522, -230, 150, -180]]
  ![![713751, -431890, 190380, -124194, 148866]] where
 M := ![![![713751, -431890, 190380, -124194, 148866]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![713751, -431890, 190380, -124194, 148866]] ![![99, -26, -64, -30, -34]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB324I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB324I1 : PrimesBelowBoundCertificateInterval O 23 61 324 where
  m := 9
  g := ![2, 2, 1, 2, 2, 1, 2, 3, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB324I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
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
    · exact ![707281, 29]
    · exact ![923521, 31]
    · exact ![69343957]
    · exact ![2825761, 41]
    · exact ![3418801, 43]
    · exact ![229345007]
    · exact ![7890481, 53]
    · exact ![3481, 3481, 59]
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
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
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
      exact NI61N1
      exact NI61N2
  β := ![I29N1, I31N1, I41N1, I43N1, I53N1, I59N2, I61N1, I61N2]
  Il := ![[I29N1], [I31N1], [], [I41N1], [I43N1], [], [I53N1], [I59N2], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
