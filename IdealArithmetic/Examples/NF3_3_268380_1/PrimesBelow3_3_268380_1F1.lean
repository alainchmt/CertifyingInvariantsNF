
import IdealArithmetic.Examples.NF3_3_268380_1.RI3_3_268380_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-78879, -5032, 1158]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-78879, -5032, 1158]] 
 ![![37, 0, 0], ![0, 37, 0], ![24, 0, 1]] where
  M :=![![![-78879, -5032, 1158], ![342768, 21867, -5032], ![-1489472, -95016, 21867]]]
  hmulB := by decide  
  f := ![![![1221, 168, -26]], ![![-7696, -1041, 168]], ![![2136, 296, -45]]]
  g := ![![![-2883, -136, 1158], ![12528, 591, -5032], ![-54440, -2568, 21867]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [8, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 36], [0, 1]]
 g := ![![[31, 34], [26], [4, 27], [10], [1]], ![[35, 3], [26], [5, 10], [10], [1]]]
 h' := ![![[11, 36], [2, 16], [5, 10], [21, 8], [29, 11], [0, 1]], ![[0, 1], [30, 21], [4, 27], [35, 29], [2, 26], [11, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [18, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [8, 26, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![600, 444, 62]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, 12, 62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1221, 168, -26]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![1221, 168, -26]] 
 ![![37, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![1221, 168, -26], ![-7696, -1041, 168], ![49728, 6920, -1041]]]
  hmulB := by decide  
  f := ![![![-78879, -5032, 1158]], ![![9264, 591, -136]], ![![-40256, -2568, 591]]]
  g := ![![![33, 168, -26], ![-208, -1041, 168], ![1344, 6920, -1041]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-78879, -5032, 1158]] ![![1221, 168, -26]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -26, 4]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-179, -26, 4]] 
 ![![41, 0, 0], ![0, 41, 0], ![27, 14, 1]] where
  M :=![![![-179, -26, 4], ![1184, 169, -26], ![-7696, -1078, 169]]]
  hmulB := by decide  
  f := ![![![13, 2, 0]], ![![0, 13, 2]], ![![23, 10, 1]]]
  g := ![![![-7, -2, 4], ![46, 13, -26], ![-299, -84, 169]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [38, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 40], [0, 1]]
 g := ![![[14, 21], [39], [33], [7, 1], [1]], ![[35, 20], [39], [33], [8, 40], [1]]]
 h' := ![![[1, 40], [2, 29], [7, 11], [21, 19], [3, 1], [0, 1]], ![[0, 1], [31, 12], [18, 30], [40, 22], [4, 40], [1, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [19, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [38, 40, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3553, 1544, 901]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-680, -270, 901]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -2, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-13, -2, 0]] 
 ![![41, 0, 0], ![27, 1, 0], ![9, 0, 1]] where
  M :=![![![-13, -2, 0], ![0, -13, -2], ![-592, -174, -13]]]
  hmulB := by decide  
  f := ![![![179, 26, -4]], ![![89, 13, -2]], ![![227, 32, -5]]]
  g := ![![![1, -2, 0], ![9, -13, -2], ![103, -174, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-179, -26, 4]] ![![-13, -2, 0]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189229, -73291, -6845]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-189229, -73291, -6845]] 
 ![![43, 0, 0], ![22, 1, 0], ![32, 0, 1]] where
  M :=![![![-189229, -73291, -6845], ![-2026120, -784744, -73291], ![-21694136, -8402437, -784744]]]
  hmulB := by decide  
  f := ![![![135369, 8761, -1999]], ![![55498, 3586, -819]], ![![161048, 10485, -2384]]]
  g := ![![![38191, -73291, -6845], ![408920, -784744, -73291], ![4378402, -8402437, -784744]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![611, 236, 22]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![611, 236, 22]] 
 ![![43, 0, 0], ![27, 1, 0], ![2, 0, 1]] where
  M :=![![![611, 236, 22], ![6512, 2525, 236], ![69856, 27044, 2525]]]
  hmulB := by decide  
  f := ![![![-6759, -932, 146]], ![![-3239, -447, 70]], ![![-6730, -924, 145]]]
  g := ![![![-135, 236, 22], ![-1445, 2525, 236], ![-15474, 27044, 2525]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-26225, -1673, 385]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![-26225, -1673, 385]] 
 ![![43, 0, 0], ![37, 1, 0], ![7, 0, 1]] where
  M :=![![![-26225, -1673, 385], ![113960, 7270, -1673], ![-495208, -31591, 7270]]]
  hmulB := by decide  
  f := ![![![1157, 175, -21]], ![![851, 135, -14]], ![![1393, 238, -19]]]
  g := ![![![767, -1673, 385], ![-3333, 7270, -1673], ![14483, -31591, 7270]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-189229, -73291, -6845]] ![![611, 236, 22]]
  ![![-1071054231, -414833999, -38743339]] where
 M := ![![![-1071054231, -414833999, -38743339]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-1071054231, -414833999, -38743339]] ![![-26225, -1673, 385]]
  ![![43, 0, 0]] where
 M := ![![![-73898553, -28621918, -2673138]]]
 hmul := by decide  
 g := ![![![![-1718571, -665626, -62166]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![396787, 153681, 14353]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![396787, 153681, 14353]] 
 ![![47, 0, 0], ![0, 47, 0], ![19, 23, 1]] where
  M :=![![![396787, 153681, 14353], ![4248488, 1645498, 153681], ![45489576, 17618735, 1645498]]]
  hmulB := by decide  
  f := ![![![24373, 1589, -361]], ![![-106856, -7034, 1589]], ![![-32431, -2132, 482]]]
  g := ![![![2640, -3754, 14353], ![28267, -40195, 153681], ![302662, -430377, 1645498]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [21, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 46], [0, 1]]
 g := ![![[44, 9], [38, 27], [33, 42], [40, 21], [1]], ![[0, 38], [0, 20], [0, 5], [0, 26], [1]]]
 h' := ![![[16, 46], [1, 44], [12, 11], [6, 29], [26, 16], [0, 1]], ![[0, 1], [0, 3], [0, 36], [0, 18], [0, 31], [16, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [46, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [21, 31, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1541, 25, 185]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -90, 185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-24373, -1589, 361]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-24373, -1589, 361]] 
 ![![47, 0, 0], ![24, 1, 0], ![35, 0, 1]] where
  M :=![![![-24373, -1589, 361], ![106856, 7034, -1589], ![-470344, -31387, 7034]]]
  hmulB := by decide  
  f := ![![![-396787, -153681, -14353]], ![![-293008, -113486, -10599]], ![![-1263343, -489310, -45699]]]
  g := ![![![24, -1589, 361], ![-135, 7034, -1589], ![782, -31387, 7034]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![396787, 153681, 14353]] ![![-24373, -1589, 361]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2271, 885, 83]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![2271, 885, 83]] 
 ![![53, 0, 0], ![0, 53, 0], ![28, 3, 1]] where
  M :=![![![2271, 885, 83], ![24568, 9492, 885], ![261960, 101563, 9492]]]
  hmulB := by decide  
  f := ![![![-4053, -553, 87]], ![![25752, 3516, -553]], ![![-3772, -515, 81]]]
  g := ![![![-1, 12, 83], ![-4, 129, 885], ![-72, 1379, 9492]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [2, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 52], [0, 1]]
 g := ![![[36, 15], [16], [30, 28], [38], [34, 1]], ![[16, 38], [16], [28, 25], [38], [15, 52]]]
 h' := ![![[34, 52], [17, 11], [46, 4], [43, 9], [38, 41], [0, 1]], ![[0, 1], [20, 42], [23, 49], [31, 44], [1, 12], [34, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [4, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [2, 19, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1754, 2163, 721]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-414, 0, 721]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4053, -553, 87]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-4053, -553, 87]] 
 ![![53, 0, 0], ![50, 1, 0], ![44, 0, 1]] where
  M :=![![![-4053, -553, 87], ![25752, 3516, -553], ![-163688, -22359, 3516]]]
  hmulB := by decide  
  f := ![![![2271, 885, 83]], ![![2606, 1014, 95]], ![![6828, 2651, 248]]]
  g := ![![![373, -553, 87], ![-2372, 3516, -553], ![15086, -22359, 3516]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![2271, 885, 83]] ![![-4053, -553, 87]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [33, 45, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 20, 18], [8, 38, 41], [0, 1]]
 g := ![![[52, 24, 17], [52, 11, 17], [6, 49], [44, 52, 9], [1]], ![[32, 34, 52, 33], [31, 56, 51, 58], [52, 5], [29, 8, 1, 55], [8, 41, 2, 50]], ![[12, 52, 3, 21], [46, 5, 51, 19], [52, 1], [22, 22, 20, 21], [44, 46, 29, 9]]]
 h' := ![![[54, 20, 18], [54, 9, 28], [36, 26, 31], [23, 48, 52], [26, 14, 3], [0, 1]], ![[8, 38, 41], [34, 43, 46], [58, 8, 53], [57, 6, 8], [24, 23, 12], [54, 20, 18]], ![[0, 1], [16, 7, 44], [0, 25, 34], [51, 5, 58], [4, 22, 44], [8, 38, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 40], []]
 b := ![[], [31, 21, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [33, 45, 56, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-131983, -48911, -3835]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2237, -829, -65]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [17, 23, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 32, 21], [45, 28, 40], [0, 1]]
 g := ![![[3, 22, 22], [42, 4], [49, 49, 25], [33, 60, 36], [1]], ![[59, 9, 50, 23], [32, 36], [59, 9, 54, 28], [32, 4, 13, 43], [5, 56, 7, 50]], ![[54, 17, 12, 35], [48, 3], [20, 0, 20, 18], [23, 59, 0, 32], [58, 58, 12, 11]]]
 h' := ![![[10, 32, 21], [32, 42, 12], [21, 14, 59], [49, 35, 56], [44, 38, 55], [0, 1]], ![[45, 28, 40], [19, 8, 59], [40, 20, 55], [5, 50, 46], [0, 54, 20], [10, 32, 21]], ![[0, 1], [39, 11, 51], [60, 27, 8], [55, 37, 20], [42, 30, 47], [45, 28, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 44], []]
 b := ![[], [49, 16, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [17, 23, 6, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3687023, 1433378, 122732]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![60443, 23498, 2012]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, -22, 2]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-133, -22, 2]] 
 ![![67, 0, 0], ![0, 67, 0], ![34, 56, 1]] where
  M :=![![![-133, -22, 2], ![592, 41, -22], ![-6512, -1322, 41]]]
  hmulB := by decide  
  f := ![![![409, 26, -6]], ![![-1776, -113, 26]], ![![-1162, -74, 17]]]
  g := ![![![-3, -2, 2], ![20, 19, -22], ![-118, -54, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [26, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 66], [0, 1]]
 g := ![![[6, 49], [25, 59], [23], [33], [15], [1]], ![[0, 18], [0, 8], [23], [33], [15], [1]]]
 h' := ![![[45, 66], [20, 7], [9, 40], [2, 36], [18, 10], [41, 45], [0, 1]], ![[0, 1], [0, 60], [0, 27], [14, 31], [66, 57], [56, 22], [45, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [1, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [26, 22, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1771, -166, 76]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65, -66, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-409, -26, 6]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-409, -26, 6]] 
 ![![67, 0, 0], ![11, 1, 0], ![13, 0, 1]] where
  M :=![![![-409, -26, 6], ![1776, 113, -26], ![-7696, -486, 113]]]
  hmulB := by decide  
  f := ![![![133, 22, -2]], ![![13, 3, 0]], ![![123, 24, -1]]]
  g := ![![![-3, -26, 6], ![13, 113, -26], ![-57, -486, 113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-133, -22, 2]] ![![-409, -26, 6]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3643731, 1411267, 131805]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![3643731, 1411267, 131805]] 
 ![![71, 0, 0], ![10, 1, 0], ![42, 0, 1]] where
  M :=![![![3643731, 1411267, 131805], ![39014280, 15110766, 1411267], ![417735032, 161794509, 15110766]]]
  hmulB := by decide  
  f := ![![![-2226147, -141777, 32659]], ![![-177386, -11304, 2603]], ![![-1907946, -121439, 27984]]]
  g := ![![![-225419, 1411267, 131805], ![-2413614, 15110766, 1411267], ![-25843130, 161794509, 15110766]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3491, 477, -75]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![3491, 477, -75]] 
 ![![71, 0, 0], ![51, 1, 0], ![26, 0, 1]] where
  M :=![![![3491, 477, -75], ![-22200, -3034, 477], ![141192, 19299, -3034]]]
  hmulB := by decide  
  f := ![![![-467, -207, -21]], ![![-423, -181, -18]], ![![-1034, -417, -40]]]
  g := ![![![-266, 477, -75], ![1692, -3034, 477], ![-10763, 19299, -3034]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![3643731, 1411267, 131805]] ![![3643731, 1411267, 131805]]
  ![![123395907385881, 47792927976444, 4463611022374]] where
 M := ![![![123395907385881, 47792927976444, 4463611022374]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI71N1 : IdealMulLeCertificate' Table 
  ![![123395907385881, 47792927976444, 4463611022374]] ![![3491, 477, -75]]
  ![![71, 0, 0]] where
 M := ![![![-1720921916421, -666536670033, -62251060003]]]
 hmul := by decide  
 g := ![![![![-24238336851, -9387840423, -876775493]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [19, 16, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 45, 48], [1, 27, 25], [0, 1]]
 g := ![![[24, 67, 9], [16, 37], [35, 3], [45, 17, 69], [56, 1], []], ![[55, 72, 38, 24], [64, 65], [49, 18], [19, 3, 9, 54], [14, 72], [46, 41]], ![[55, 35, 30, 46], [62, 64], [57, 4], [14, 5, 43, 41], [36, 54], [69, 41]]]
 h' := ![![[55, 45, 48], [13, 12, 70], [68, 27, 16], [21, 64, 52], [31, 34, 54], [0, 0, 1], [0, 1]], ![[1, 27, 25], [60, 17, 57], [53, 38, 49], [53, 22, 23], [14, 67, 24], [34, 4, 27], [55, 45, 48]], ![[0, 1], [13, 44, 19], [13, 8, 8], [1, 60, 71], [62, 45, 68], [4, 69, 45], [1, 27, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 14], []]
 b := ![[], [24, 54, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [19, 16, 17, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1030395, 530783, 70591]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14115, 7271, 967]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23609, 9144, 854]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![23609, 9144, 854]] 
 ![![79, 0, 0], ![0, 79, 0], ![64, 54, 1]] where
  M :=![![![23609, 9144, 854], ![252784, 97907, 9144], ![2706624, 1048312, 97907]]]
  hmulB := by decide  
  f := ![![![199, -40, 2]], ![![592, 373, -40]], ![![416, 186, -21]]]
  g := ![![![-393, -468, 854], ![-4208, -5011, 9144], ![-45056, -53654, 97907]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [18, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 78], [0, 1]]
 g := ![![[55, 22], [36, 46], [30, 31], [46, 72], [26], [1]], ![[0, 57], [0, 33], [71, 48], [24, 7], [26], [1]]]
 h' := ![![[37, 78], [63, 41], [13, 21], [41, 49], [14, 25], [61, 37], [0, 1]], ![[0, 1], [0, 38], [0, 58], [37, 30], [70, 54], [8, 42], [37, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [49, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [18, 42, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11734, -2756, 540]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-586, -404, 540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-199, 40, -2]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-199, 40, -2]] 
 ![![79, 0, 0], ![25, 1, 0], ![7, 0, 1]] where
  M :=![![![-199, 40, -2], ![-592, -373, 40], ![11840, 2888, -373]]]
  hmulB := by decide  
  f := ![![![-23609, -9144, -854]], ![![-10671, -4133, -386]], ![![-36353, -14080, -1315]]]
  g := ![![![-15, 40, -2], ![107, -373, 40], ![-731, 2888, -373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![23609, 9144, 854]] ![![-199, 40, -2]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB116I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB116I1 : PrimesBelowBoundCertificateInterval O 31 79 116 where
  m := 11
  g := ![2, 2, 3, 2, 2, 1, 1, 2, 3, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB116I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
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
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![389017]
    · exact ![6241, 79]
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
      exact NI43N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I43N0, I43N1, I43N2, I47N1, I53N1, I67N1, I71N0, I71N1, I79N1]
  Il := ![[I37N1], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [], [], [I67N1], [I71N0, I71N0, I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
