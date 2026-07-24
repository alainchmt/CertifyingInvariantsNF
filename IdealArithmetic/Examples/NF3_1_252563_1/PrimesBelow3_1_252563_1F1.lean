
import IdealArithmetic.Examples.NF3_1_252563_1.RI3_1_252563_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![1, 1, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![1, 1, 0]] 
 ![![37, 0, 0], ![1, 1, 0], ![36, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![1, 1, 0], ![0, 1, 1], ![35, -38, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![37, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![36, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 37, 0], ![-36, 0, 37]], ![![0, 1, 0], ![-1, 1, 1], ![1, -38, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3494298596, 81183911, 90028698]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![3494298596, 81183911, 90028698]] 
 ![![37, 0, 0], ![8, 1, 0], ![10, 0, 1]] where
  M :=![![![3494298596, 81183911, 90028698], ![3151004430, 73208072, 81183911], ![2841436885, 66015812, 73208072]]]
  hmulB := by decide  
  f := ![![![-43548, 43184, 5665]], ![![-4057, 2342, 2392]], ![![29080, -27321, -5464]]]
  g := ![![![52555144, 81183911, 90028698], ![47391912, 73208072, 81183911], ![42735937, 66015812, 73208072]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-9, 1, 0]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-9, 1, 0]] 
 ![![37, 0, 0], ![28, 1, 0], ![30, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-9, 1, 0], ![0, -9, 1], ![35, -38, -9]]]
  hmulB := by decide  
  f := ![![![316, -35, 0], ![1295, 0, 0]], ![![244, -27, 0], ![1000, 0, 0]], ![![264, -29, 0], ![1082, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 37, 0], ![-30, 0, 37]], ![![-1, 1, 0], ![6, -9, 1], ![37, -38, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![1, 1, 0]] ![![3494298596, 81183911, 90028698]]
  ![![37, 0, 0], ![8, 9, 1]] where
 M := ![![![129289048052, 3003804707, 3331061826]], ![![6645303026, 154391983, 171212609]]]
 hmul := by decide  
 g := ![![![![3342351012, -89757121, 71035250], ![702757576, 0, 0]]], ![![![171792858, -4613411, 3651127], ![36120910, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![8, 9, 1]] ![![37, 0, 0], ![-9, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-333, 37, 0]], ![![296, 333, 37], ![-37, -111, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-9, 1, 0]]], ![![![8, 9, 1]], ![![-1, -3, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![5, 7, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![5, 7, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![5, 7, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![5, 7, 1], ![35, -33, 7], ![245, -231, -33]]]
  hmulB := by decide  
  f := ![![![-4, -7, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -7, 41]], ![![0, 0, 1], ![0, -2, 7], ![10, 0, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [36, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40], [0, 1]]
 g := ![![[10, 8], [25], [39], [40, 40], [1]], ![[0, 33], [25], [39], [31, 1], [1]]]
 h' := ![![[9, 40], [22, 34], [15, 36], [36, 11], [5, 9], [0, 1]], ![[0, 1], [0, 7], [11, 5], [12, 30], [4, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [35, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [36, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106, -73, -69]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 10, -69]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-7, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-7, 1, 0]] 
 ![![41, 0, 0], ![34, 1, 0], ![33, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-7, 1, 0], ![0, -7, 1], ![35, -38, -7]]]
  hmulB := by decide  
  f := ![![![57, -8, 0], ![328, 0, 0]], ![![50, -7, 0], ![288, 0, 0]], ![![51, -7, 0], ![294, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 41, 0], ![-33, 0, 41]], ![![-1, 1, 0], ![5, -7, 1], ![38, -38, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![5, 7, 1]] ![![41, 0, 0], ![-7, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-287, 41, 0]], ![![205, 287, 41], ![0, -82, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-7, 1, 0]]], ![![![5, 7, 1]], ![![0, -2, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51613357, -1199146, -1329790]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-51613357, -1199146, -1329790]] 
 ![![43, 0, 0], ![0, 43, 0], ![19, 29, 1]] where
  M :=![![![-51613357, -1199146, -1329790], ![-46542650, -1081337, -1199146], ![-41970110, -975102, -1081337]]]
  hmulB := by decide  
  f := ![![![-1039, 1154, -2]], ![![-70, -963, 1154]], ![![433, -1161, 755]]]
  g := ![![![-612729, 868948, -1329790], ![-552532, 783579, -1199146], ![-498249, 706597, -1081337]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [37, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 42], [0, 1]]
 g := ![![[31, 25], [4, 40], [15], [31, 24], [1]], ![[37, 18], [5, 3], [15], [23, 19], [1]]]
 h' := ![![[14, 42], [24, 5], [28, 30], [14, 12], [6, 14], [0, 1]], ![[0, 1], [8, 38], [18, 13], [10, 31], [30, 29], [14, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [20, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [37, 29, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-411, 717, -257]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![104, 190, -257]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1039, 1154, -2]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-1039, 1154, -2]] 
 ![![43, 0, 0], ![14, 1, 0], ![19, 0, 1]] where
  M :=![![![-1039, 1154, -2], ![-70, -963, 1154], ![40390, -43922, -963]]]
  hmulB := by decide  
  f := ![![![-51613357, -1199146, -1329790]], ![![-17886736, -415567, -460842]], ![![-23781951, -552532, -612729]]]
  g := ![![![-399, 1154, -2], ![-198, -963, 1154], ![15665, -43922, -963]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-51613357, -1199146, -1329790]] ![![-1039, 1154, -2]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2082, 171, -2750]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![2082, 171, -2750]] 
 ![![47, 0, 0], ![0, 47, 0], ![19, 34, 1]] where
  M :=![![![2082, 171, -2750], ![-96250, 106582, 171], ![5985, -102748, 106582]]]
  hmulB := by decide  
  f := ![![![242070056, 5624074, 6236803]], ![![218288105, 5071542, 5624074]], ![![259956792, 6039641, 6697645]]]
  g := ![![![1156, 1993, -2750], ![-2117, 2144, 171], ![-42959, -79288, 106582]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [31, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 46], [0, 1]]
 g := ![![[14, 27], [36, 25], [43, 14], [9, 27], [1]], ![[46, 20], [43, 22], [30, 33], [41, 20], [1]]]
 h' := ![![[36, 46], [12, 11], [30, 42], [3, 25], [16, 36], [0, 1]], ![[0, 1], [32, 36], [38, 5], [10, 22], [43, 11], [36, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [35, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [31, 11, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3353, -6, 80]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39, -58, 80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-242070056, -5624074, -6236803]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-242070056, -5624074, -6236803]] 
 ![![47, 0, 0], ![13, 1, 0], ![19, 0, 1]] where
  M :=![![![-242070056, -5624074, -6236803], ![-218288105, -5071542, -5624074], ![-196842590, -4573293, -5071542]]]
  hmulB := by decide  
  f := ![![![-2082, -171, 2750]], ![![1472, -2315, 757]], ![![-969, 2117, -1156]]]
  g := ![![![-1073571, -5624074, -6236803], ![-968099, -5071542, -5624074], ![-872989, -4573293, -5071542]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![2082, 171, -2750]] ![![-242070056, -5624074, -6236803]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![47, 3, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![47, 3, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![47, 3, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![47, 3, 1], ![35, 9, 3], ![105, -79, 9]]]
  hmulB := by decide  
  f := ![![![-46, -3, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -3, 53]], ![![0, 0, 1], ![-2, 0, 3], ![-6, -2, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [40, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 52], [0, 1]]
 g := ![![[44, 4], [44], [47, 47], [42], [42, 1]], ![[0, 49], [44], [7, 6], [42], [31, 52]]]
 h' := ![![[42, 52], [31, 51], [28, 37], [7, 10], [16, 28], [0, 1]], ![[0, 1], [0, 2], [45, 16], [3, 43], [26, 25], [42, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [3, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [40, 11, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-158, 556, -380]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![334, 32, -380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-3, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-3, 1, 0]] 
 ![![53, 0, 0], ![50, 1, 0], ![44, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-3, 1, 0], ![0, -3, 1], ![35, -38, -3]]]
  hmulB := by decide  
  f := ![![![61, -20, 0], ![1060, 0, 0]], ![![58, -19, 0], ![1008, 0, 0]], ![![52, -17, 0], ![904, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 53, 0], ![-44, 0, 53]], ![![-1, 1, 0], ![2, -3, 1], ![39, -38, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![47, 3, 1]] ![![53, 0, 0], ![-3, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-159, 53, 0]], ![![2491, 159, 53], ![-106, 0, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-3, 1, 0]]], ![![![47, 3, 1]], ![![-2, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [53, 20, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 20, 41], [27, 38, 18], [0, 1]]
 g := ![![[18, 14, 48], [10, 2, 17], [33, 21], [56, 44, 53], [1]], ![[34, 41, 19, 41], [15, 40, 48, 17], [6, 51], [30, 23, 44, 15], [8, 32, 5, 9]], ![[15, 49, 30, 6], [26, 22, 51, 8], [26, 7], [37, 37, 58, 2], [7, 58, 26, 50]]]
 h' := ![![[49, 20, 41], [1, 11, 44], [50, 17, 28], [41, 6, 32], [6, 39, 17], [0, 1]], ![[27, 38, 18], [0, 56, 58], [3, 5, 50], [12, 49, 46], [51, 14, 3], [49, 20, 41]], ![[0, 1], [53, 51, 16], [42, 37, 40], [57, 4, 40], [19, 6, 39], [27, 38, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 28], []]
 b := ![[], [17, 47, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [53, 20, 42, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5723, -3481, -3009]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![97, -59, -51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![4, 24, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![4, 24, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![4, 24, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![4, 24, 1], ![35, -34, 24], ![840, -877, -34]]]
  hmulB := by decide  
  f := ![![![-3, -24, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -24, 61]], ![![0, 0, 1], ![-1, -10, 24], ![16, -1, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [54, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 60], [0, 1]]
 g := ![![[25, 34], [16], [7, 56], [32, 39], [53, 1]], ![[58, 27], [16], [47, 5], [25, 22], [45, 60]]]
 h' := ![![[53, 60], [12, 20], [49, 4], [41, 42], [5, 10], [0, 1]], ![[0, 1], [35, 41], [17, 57], [10, 19], [47, 51], [53, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [45, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [54, 8, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1393, -1219, 333]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -151, 333]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-24, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-24, 1, 0]] 
 ![![61, 0, 0], ![37, 1, 0], ![34, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-24, 1, 0], ![0, -24, 1], ![35, -38, -24]]]
  hmulB := by decide  
  f := ![![![961, -40, 0], ![2440, 0, 0]], ![![601, -25, 0], ![1526, 0, 0]], ![![538, -22, 0], ![1366, 1, 0]]]
  g := ![![![1, 0, 0], ![-37, 61, 0], ![-34, 0, 61]], ![![-1, 1, 0], ![14, -24, 1], ![37, -38, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![4, 24, 1]] ![![61, 0, 0], ![-24, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1464, 61, 0]], ![![244, 1464, 61], ![-61, -610, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-24, 1, 0]]], ![![![4, 24, 1]], ![![-1, -10, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24376, 29186, -2389]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-24376, 29186, -2389]] 
 ![![67, 0, 0], ![0, 67, 0], ![18, 28, 1]] where
  M :=![![![-24376, 29186, -2389], ![-83615, 66406, 29186], ![1021510, -1192683, 66406]]]
  hmulB := by decide  
  f := ![![![-585364222, -13599913, -15081590]], ![![-527855650, -12263802, -13599913]], ![![-384962853, -8943938, -9918358]]]
  g := ![![![278, 1434, -2389], ![-9089, -11206, 29186], ![-2594, -45553, 66406]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [17, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 66], [0, 1]]
 g := ![![[53, 4], [28, 59], [16], [55], [29], [1]], ![[0, 63], [0, 8], [16], [55], [29], [1]]]
 h' := ![![[37, 66], [60, 2], [6, 27], [12, 63], [64, 16], [50, 37], [0, 1]], ![[0, 1], [0, 65], [0, 40], [65, 4], [53, 51], [12, 30], [37, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [42, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [17, 30, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-222, 347, -57]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 29, -57]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-585364222, -13599913, -15081590]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-585364222, -13599913, -15081590]] 
 ![![67, 0, 0], ![39, 1, 0], ![20, 0, 1]] where
  M :=![![![-585364222, -13599913, -15081590], ![-527855650, -12263802, -13599913], ![-475996955, -11058956, -12263802]]]
  hmulB := by decide  
  f := ![![![-24376, 29186, -2389]], ![![-15437, 17980, -955]], ![![7970, -9089, 278]]]
  g := ![![![3681555, -13599913, -15081590], ![3319864, -12263802, -13599913], ![2993707, -11058956, -12263802]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-24376, 29186, -2389]] ![![-585364222, -13599913, -15081590]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3881, 90, 100]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![3881, 90, 100]] 
 ![![71, 0, 0], ![0, 71, 0], ![31, 8, 1]] where
  M :=![![![3881, 90, 100], ![3500, 81, 90], ![3150, 80, 81]]]
  hmulB := by decide  
  f := ![![![-9, 10, 0]], ![![0, -9, 10]], ![![1, -2, 1]]]
  g := ![![![11, -10, 100], ![10, -9, 90], ![9, -8, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [42, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 70], [0, 1]]
 g := ![![[17, 50], [4, 2], [60, 5], [2], [16], [1]], ![[30, 21], [67, 69], [40, 66], [2], [16], [1]]]
 h' := ![![[67, 70], [45, 60], [36, 12], [6, 54], [27, 59], [29, 67], [0, 1]], ![[0, 1], [18, 11], [59, 59], [3, 17], [4, 12], [45, 4], [67, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [43, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [42, 4, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182, -8, -143]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![65, 16, -143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 10, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-9, 10, 0]] 
 ![![71, 0, 0], ![63, 1, 0], ![7, 0, 1]] where
  M :=![![![-9, 10, 0], ![0, -9, 10], ![350, -380, -9]]]
  hmulB := by decide  
  f := ![![![3881, 90, 100]], ![![3493, 81, 90]], ![![427, 10, 11]]]
  g := ![![![-9, 10, 0], ![7, -9, 10], ![343, -380, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![3881, 90, 100]] ![![-9, 10, 0]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-11, 30, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-11, 30, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![62, 30, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-11, 30, 1], ![35, -49, 30], ![1050, -1105, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -30, 73]], ![![-1, 0, 1], ![-25, -13, 30], ![56, 5, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [69, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 72], [0, 1]]
 g := ![![[26, 18], [24], [1], [35, 55], [12], [1]], ![[0, 55], [24], [1], [61, 18], [12], [1]]]
 h' := ![![[31, 72], [17, 23], [40, 43], [67, 72], [64, 36], [4, 31], [0, 1]], ![[0, 1], [0, 50], [59, 30], [36, 1], [12, 37], [16, 42], [31, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [35, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [69, 42, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1243, 1200, 40]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51, 0, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-30, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-30, 1, 0]] 
 ![![73, 0, 0], ![43, 1, 0], ![49, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-30, 1, 0], ![0, -30, 1], ![35, -38, -30]]]
  hmulB := by decide  
  f := ![![![1981, -66, 0], ![4818, 0, 0]], ![![1171, -39, 0], ![2848, 0, 0]], ![![1333, -44, 0], ![3242, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 73, 0], ![-49, 0, 73]], ![![-1, 1, 0], ![17, -30, 1], ![43, -38, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-11, 30, 1]] ![![73, 0, 0], ![-30, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-2190, 73, 0]], ![![-803, 2190, 73], ![365, -949, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-30, 1, 0]]], ![![![-11, 30, 1]], ![![5, -13, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, -348, 92]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![239, -348, 92]] 
 ![![79, 0, 0], ![9, 1, 0], ![77, 0, 1]] where
  M :=![![![239, -348, 92], ![3220, -3257, -348], ![-12180, 16444, -3257]]]
  hmulB := by decide  
  f := ![![![16330561, 379412, 420748]], ![![2046851, 47555, 52736]], ![![16085223, 373712, 414427]]]
  g := ![![![-47, -348, 92], ![751, -3257, -348], ![1147, 16444, -3257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3959, 92, 102]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![3959, 92, 102]] 
 ![![79, 0, 0], ![35, 1, 0], ![39, 0, 1]] where
  M :=![![![3959, 92, 102], ![3570, 83, 92], ![3220, 74, 83]]]
  hmulB := by decide  
  f := ![![![81, -88, -2]], ![![35, -37, -2]], ![![1, -2, 1]]]
  g := ![![![-41, 92, 102], ![-37, 83, 92], ![-33, 74, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![239, -348, 92]] ![![3959, 92, 102]]
  ![![81, -88, -2]] where
 M := ![![![81, -88, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![81, -88, -2]] ![![3959, 92, 102]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB143I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB143I1 : PrimesBelowBoundCertificateInterval O 31 79 143 where
  m := 11
  g := ![3, 2, 2, 2, 2, 1, 2, 2, 2, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB143I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N1]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I41N1, I43N1, I47N1, I53N1, I61N1, I67N1, I71N1, I73N1, I79N0, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [I41N1], [I43N1], [I47N1], [I53N1], [], [I61N1], [I67N1], [I71N1], [I73N1], [I79N0, I79N1, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
