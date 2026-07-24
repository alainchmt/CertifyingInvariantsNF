
import IdealArithmetic.Examples.NF3_1_903756_2.RI3_1_903756_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-7, -8, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-7, -8, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![30, 29, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-7, -8, 1], ![151, 14, -85], ![-1379, -22, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -29, 37]], ![![-1, -1, 1], ![73, 67, -85], ![-17, 19, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [32, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 36], [0, 1]]
 g := ![![[3, 27], [12], [6, 26], [3], [1]], ![[1, 10], [12], [26, 11], [3], [1]]]
 h' := ![![[15, 36], [35, 8], [30, 7], [3, 10], [5, 15], [0, 1]], ![[0, 1], [7, 29], [24, 30], [5, 27], [8, 22], [15, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [28, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [32, 22, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6223, 2080, 517]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-251, -349, 517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![11, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![11, 1, 0]] 
 ![![37, 0, 0], ![11, 1, 0], ![25, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![11, 1, 0], ![4, 9, 11], ![183, 5, 14]]]
  hmulB := by decide  
  f := ![![![3310, 8229, 10098], ![1221, -33966, 0]], ![![978, 2438, 2992], ![371, -10064, 0]], ![![2235, 5560, 6823], ![830, -22950, 0]]]
  g := ![![![1, 0, 0], ![-11, 37, 0], ![-25, 0, 37]], ![![0, 1, 0], ![-10, 9, 11], ![-6, 5, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-7, -8, 1]] ![![37, 0, 0], ![11, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![407, 37, 0]], ![![-259, -296, 37], ![74, -74, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![11, 1, 0]]], ![![![-7, -8, 1]], ![![2, -2, -2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30, -1, 2]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-30, -1, 2]] 
 ![![41, 0, 0], ![0, 41, 0], ![26, 20, 1]] where
  M :=![![![-30, -1, 2], ![362, -18, -5], ![-13, 31, -21]]]
  hmulB := by decide  
  f := ![![![-13, -1, -1]], ![![-187, -16, -14]], ![![-106, -9, -8]]]
  g := ![![![-2, -1, 2], ![12, 2, -5], ![13, 11, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [14, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 40], [0, 1]]
 g := ![![[6, 25], [40], [9], [7, 4], [1]], ![[38, 16], [40], [9], [40, 37], [1]]]
 h' := ![![[39, 40], [22, 5], [7, 9], [25, 3], [27, 39], [0, 1]], ![[0, 1], [12, 36], [30, 32], [19, 38], [31, 2], [39, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [30, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [14, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10616, 9262, 3739]
  a := ![9, -7, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2630, -1598, 3739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 1, 1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![13, 1, 1]] 
 ![![41, 0, 0], ![23, 1, 0], ![31, 0, 1]] where
  M :=![![![13, 1, 1], ![187, 16, 14], ![268, 23, 22]]]
  hmulB := by decide  
  f := ![![![30, 1, -2]], ![![8, 1, -1]], ![![23, 0, -1]]]
  g := ![![![-1, 1, 1], ![-15, 16, 14], ![-23, 23, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-30, -1, 2]] ![![13, 1, 1]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-599207, -76851, 78801]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-599207, -76851, 78801]] 
 ![![43, 0, 0], ![0, 43, 0], ![24, 34, 1]] where
  M :=![![![-599207, -76851, 78801], ![14113179, -51500, -608958], ![-7365648, 1034163, -356954]]]
  hmulB := by decide  
  f := ![![![15073138678, 1257228063, 1182727506]], ![![221468045850, 18472320082, 17377691211]], ![![191215661877, 15949013761, 15003910447]]]
  g := ![![![-57917, -64095, 78801], ![668097, 480304, -608958], ![27936, 306293, -356954]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [14, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 42], [0, 1]]
 g := ![![[7, 40], [38, 13], [36], [27, 15], [1]], ![[0, 3], [11, 30], [36], [19, 28], [1]]]
 h' := ![![[31, 42], [27, 13], [7, 20], [9, 6], [29, 31], [0, 1]], ![[0, 1], [0, 30], [25, 23], [23, 37], [1, 12], [31, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [37, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [14, 12, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10478993, 4538674, 1679047]
  a := ![-196, 67, -523]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-693445, -1222068, 1679047]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15073138678, 1257228063, 1182727506]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![15073138678, 1257228063, 1182727506]] 
 ![![43, 0, 0], ![10, 1, 0], ![40, 0, 1]] where
  M :=![![![15073138678, 1257228063, 1182727506], ![221468045850, 18472320082, 17377691211], ![330604573539, 27575235423, 25941187903]]]
  hmulB := by decide  
  f := ![![![-599207, -76851, 78801]], ![![188863, -19070, 4164]], ![![-728696, -47439, 65002]]]
  g := ![![![-1042052144, 1257228063, 1182727506], ![-15310762870, 18472320082, 17377691211], ![-22855704577, 27575235423, 25941187903]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-599207, -76851, 78801]] ![![15073138678, 1257228063, 1182727506]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![22, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![22, 1, 0]] 
 ![![47, 0, 0], ![22, 1, 0], ![33, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![22, 1, 0], ![4, 20, 11], ![183, 5, 25]]]
  hmulB := by decide  
  f := ![![![-935, -5988, -3300], ![-564, 14100, 0]], ![![-450, -2795, -1540], ![-234, 6580, 0]], ![![-671, -4205, -2317], ![-365, 9900, 0]]]
  g := ![![![1, 0, 0], ![-22, 47, 0], ![-33, 0, 47]], ![![0, 1, 0], ![-17, 20, 11], ![-16, 5, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-16, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-16, 1, 0]] 
 ![![47, 0, 0], ![31, 1, 0], ![34, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-16, 1, 0], ![4, -18, 11], ![183, 5, -13]]]
  hmulB := by decide  
  f := ![![![5953, -30831, 18876], ![-2679, -80652, 0]], ![![3933, -20321, 12441], ![-1738, -53157, 0]], ![![4318, -22304, 13655], ![-1904, -58344, 0]]]
  g := ![![![1, 0, 0], ![-31, 47, 0], ![-34, 0, 47]], ![![-1, 1, 0], ![4, -18, 11], ![10, 5, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-7, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-7, 1, 0]] 
 ![![47, 0, 0], ![40, 1, 0], ![16, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-7, 1, 0], ![4, -9, 11], ![183, 5, -4]]]
  hmulB := by decide  
  f := ![![![1479, -3414, 4180], ![-282, -17860, 0]], ![![1258, -2902, 3553], ![-234, -15181, 0]], ![![509, -1163, 1423], ![-59, -6080, 0]]]
  g := ![![![1, 0, 0], ![-40, 47, 0], ![-16, 0, 47]], ![![-1, 1, 0], ![4, -9, 11], ![1, 5, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![22, 1, 0]] ![![47, 0, 0], ![-16, 1, 0]]
  ![![47, 0, 0], ![-6, -21, 1]] where
 M := ![![![2209, 0, 0], ![-752, 47, 0]], ![![1034, 47, 0], ![-348, 4, 11]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![-10, 22, -1], ![47, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![-6, 5, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-6, -21, 1]] ![![47, 0, 0], ![-7, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-329, 47, 0]], ![![-282, -987, 47], ![141, 188, -235]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-7, 1, 0]]], ![![![-6, -21, 1]], ![![3, 4, -5]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![9, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![9, 1, 0]] 
 ![![53, 0, 0], ![9, 1, 0], ![38, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![9, 1, 0], ![4, 7, 11], ![183, 5, 12]]]
  hmulB := by decide  
  f := ![![![-581, -1048, -1650], ![-106, 7950, 0]], ![![-100, -175, -275], ![1, 1325, 0]], ![![-422, -752, -1183], ![-44, 5700, 0]]]
  g := ![![![1, 0, 0], ![-9, 53, 0], ![-38, 0, 53]], ![![0, 1, 0], ![-9, 7, 11], ![-6, 5, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-5, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-5, 1, 0]] 
 ![![53, 0, 0], ![48, 1, 0], ![2, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-5, 1, 0], ![4, -7, 11], ![183, 5, -2]]]
  hmulB := by decide  
  f := ![![![3820, -6753, 10626], ![-477, -51198, 0]], ![![3457, -6110, 9614], ![-423, -46322, 0]], ![![145, -255, 401], ![-9, -1932, 0]]]
  g := ![![![1, 0, 0], ![-48, 53, 0], ![-2, 0, 53]], ![![-1, 1, 0], ![6, -7, 11], ![-1, 5, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![9, 1, 0]] ![![53, 0, 0], ![-5, 1, 0]]
  ![![53, 0, 0], ![-23, 5, 1]] where
 M := ![![![2809, 0, 0], ![-265, 53, 0]], ![![477, 53, 0], ![-41, 2, 11]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![18, -4, -1], ![53, 0, 0]]], ![![![9, 1, 0], ![0, 0, 0]], ![![4, -1, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-23, 5, 1]] ![![53, 0, 0], ![-5, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-265, 53, 0]], ![![-1219, 265, 53], ![318, -53, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-5, 1, 0]]], ![![![-23, 5, 1]], ![![6, -1, 1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![19, -25, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![19, -25, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![19, 34, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![19, -25, 1], ![83, 74, -272], ![-4490, -107, -50]]]
  hmulB := by decide  
  f := ![![![-18, 25, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -34, 59]], ![![0, -1, 1], ![89, 158, -272], ![-60, 27, -50]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [50, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 58], [0, 1]]
 g := ![![[4, 27], [53, 21], [26], [46, 49], [36, 1]], ![[32, 32], [42, 38], [26], [40, 10], [13, 58]]]
 h' := ![![[36, 58], [5, 33], [58, 27], [1, 47], [29, 7], [0, 1]], ![[0, 1], [13, 26], [27, 32], [41, 12], [45, 52], [36, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [8, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [50, 23, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1707, 9708, 3121]
  a := ![-9, 6, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1034, -1634, 3121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-23, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-23, 1, 0]] 
 ![![59, 0, 0], ![36, 1, 0], ![50, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-23, 1, 0], ![4, -25, 11], ![183, 5, -20]]]
  hmulB := by decide  
  f := ![![![7385, -55286, 24354], ![-3776, -130626, 0]], ![![4504, -33711, 14850], ![-2300, -79650, 0]], ![![6269, -46853, 20639], ![-3173, -110700, 0]]]
  g := ![![![1, 0, 0], ![-36, 59, 0], ![-50, 0, 59]], ![![-1, 1, 0], ![6, -25, 11], ![17, 5, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![19, -25, 1]] ![![59, 0, 0], ![-23, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1357, 59, 0]], ![![1121, -1475, 59], ![-354, 649, -295]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-23, 1, 0]]], ![![![19, -25, 1]], ![![-6, 11, -5]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [46, 7, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 16, 18], [29, 44, 43], [0, 1]]
 g := ![![[34, 57, 48], [49, 47], [0, 36, 36], [24, 55, 39], [1]], ![[48, 34, 24, 38], [24, 14], [25, 51, 36, 44], [12, 37, 3, 17], [27, 5, 54, 37]], ![[55, 26, 52, 32], [43, 58], [23, 37, 27, 30], [9, 24, 31, 54], [55, 43, 11, 24]]]
 h' := ![![[22, 16, 18], [3, 57, 32], [0, 27, 13], [55, 28, 55], [15, 54, 51], [0, 1]], ![[29, 44, 43], [54, 20, 55], [50, 1, 21], [54, 51, 57], [12, 60, 44], [22, 16, 18]], ![[0, 1], [60, 45, 35], [5, 33, 27], [53, 43, 10], [21, 8, 27], [29, 44, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 57], []]
 b := ![[], [43, 20, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [46, 7, 10, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4667598, -245159, -157685]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76518, -4019, -2585]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-15, -18, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-15, -18, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![52, 49, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-15, -18, 1], ![111, 26, -195], ![-3209, -72, -63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -49, 67]], ![![-1, -1, 1], ![153, 143, -195], ![1, 45, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 66], [0, 1]]
 g := ![![[0, 17], [], [], [], [], [1]], ![[0, 50], [], [], [], [], [1]]]
 h' := ![![[0, 66], [0, 33], [10], [55], [16], [63], [0, 1]], ![[0, 1], [0, 34], [10], [55], [16], [63], [0, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [0, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [4, 0, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![143026, 9250, 7072]
  a := ![7, 16, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3354, -5034, 7072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-6, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-6, 1, 0]] 
 ![![67, 0, 0], ![61, 1, 0], ![63, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-6, 1, 0], ![4, -8, 11], ![183, 5, -3]]]
  hmulB := by decide  
  f := ![![![-2521, 5099, -7018], ![335, 42746, 0]], ![![-2289, 4635, -6380], ![336, 38860, 0]], ![![-2373, 4795, -6599], ![287, 40194, 0]]]
  g := ![![![1, 0, 0], ![-61, 67, 0], ![-63, 0, 67]], ![![-1, 1, 0], ![-3, -8, 11], ![1, 5, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-15, -18, 1]] ![![67, 0, 0], ![-6, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-402, 67, 0]], ![![-1005, -1206, 67], ![201, 134, -201]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-6, 1, 0]]], ![![![-15, -18, 1]], ![![3, 2, -3]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [32, 55, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 28, 54], [17, 42, 17], [0, 1]]
 g := ![![[63, 9, 58], [10, 55, 64], [53, 59, 5], [30, 25], [60, 1], []], ![[2, 47, 7, 9], [61, 3, 4, 64], [25, 65, 4, 30], [31, 50], [16, 60], [58, 5]], ![[59, 36, 17, 52], [39, 38, 1, 13], [30, 60, 21, 22], [12, 43], [37, 3], [24, 5]]]
 h' := ![![[43, 28, 54], [35, 26, 22], [8, 28, 63], [43, 5, 54], [68, 5, 66], [0, 0, 1], [0, 1]], ![[17, 42, 17], [5, 26, 56], [61, 13, 40], [22, 37, 53], [34, 22, 60], [64, 52, 42], [43, 28, 54]], ![[0, 1], [21, 19, 64], [56, 30, 39], [35, 29, 35], [63, 44, 16], [18, 19, 28], [17, 42, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 48], []]
 b := ![[], [28, 26, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [32, 55, 11, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19114691, -1269480, 54599]
  a := ![-7, 6, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-269221, -17880, 769]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [72, 6, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 22, 53], [57, 50, 20], [0, 1]]
 g := ![![[60, 54, 65], [63, 64], [28, 27], [48, 46, 2], [44, 1], []], ![[14, 72, 54, 13], [9, 72], [62, 69], [14, 15, 11, 66], [42, 18], [3, 35]], ![[24, 56, 37, 58], [47, 57], [18, 8], [28, 35, 68, 42], [18, 46], [36, 35]]]
 h' := ![![[60, 22, 53], [6, 25, 49], [69, 58, 65], [48, 15, 10], [44, 29, 32], [0, 0, 1], [0, 1]], ![[57, 50, 20], [6, 0, 52], [56, 22, 46], [40, 36, 54], [61, 33, 71], [26, 29, 50], [60, 22, 53]], ![[0, 1], [44, 48, 45], [17, 66, 35], [27, 22, 9], [18, 11, 43], [0, 44, 22], [57, 50, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 65], []]
 b := ![[], [27, 39, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [72, 6, 29, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36596871, 2297967, 1112958]
  a := ![8, -3, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![501327, 31479, 15246]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [8, 63, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 10, 41], [10, 68, 38], [0, 1]]
 g := ![![[2, 21, 8], [8, 15, 45], [34, 15, 11], [33, 57, 18], [73, 1], []], ![[38, 75, 49, 35], [57, 11, 75, 47], [13, 76, 47, 54], [18, 5, 16, 78], [33, 42], [56, 22]], ![[25, 30, 23, 42], [26, 20, 17, 38], [14, 18, 46, 51], [12, 74, 73, 19], [11, 21], [59, 22]]]
 h' := ![![[63, 10, 41], [15, 48, 18], [44, 47, 19], [52, 6, 66], [48, 54, 52], [0, 0, 1], [0, 1]], ![[10, 68, 38], [57, 17, 32], [68, 12, 59], [3, 74, 73], [23, 10, 62], [45, 5, 68], [63, 10, 41]], ![[0, 1], [40, 14, 29], [3, 20, 1], [50, 78, 19], [46, 15, 44], [23, 74, 10], [10, 68, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 37], []]
 b := ![[], [35, 52, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [8, 63, 6, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-219288437, -12372585, -6567270]
  a := ![-15, 5, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2775803, -156615, -83130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB269I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB269I1 : PrimesBelowBoundCertificateInterval O 31 79 269 where
  m := 11
  g := ![2, 2, 2, 3, 3, 2, 1, 2, 1, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB269I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![389017]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
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
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N1, I41N1, I43N1, I47N0, I47N1, I47N2, I53N0, I53N1, I59N1, I67N1]
  Il := ![[I37N1], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [I53N0, I53N1, I53N1], [I59N1], [], [I67N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
