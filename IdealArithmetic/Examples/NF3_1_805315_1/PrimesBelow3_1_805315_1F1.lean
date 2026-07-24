
import IdealArithmetic.Examples.NF3_1_805315_1.RI3_1_805315_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [20, 8, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 25, 24], [16, 11, 13], [0, 1]]
 g := ![![[3, 35, 4], [6, 4], [20, 28, 16], [30, 1], []], ![[5, 9, 22, 29], [7, 16], [9, 14, 10, 17], [27, 10], [17, 21]], ![[8, 1, 10, 29], [10, 36], [4, 1, 10, 14], [6, 33], [28, 21]]]
 h' := ![![[14, 25, 24], [3, 12, 35], [7, 10, 35], [29, 36, 4], [0, 0, 1], [0, 1]], ![[16, 11, 13], [15, 12, 7], [28, 36, 33], [31, 33, 20], [4, 33, 11], [14, 25, 24]], ![[0, 1], [26, 13, 32], [35, 28, 6], [18, 5, 13], [29, 4, 25], [16, 11, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 22], []]
 b := ![[], [9, 36, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [20, 8, 7, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5057604, 1379434, -455840]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-136692, 37282, -12320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1773105986839529704079233, -320601084919121793296749, 113664148727066581700576]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1773105986839529704079233, -320601084919121793296749, 113664148727066581700576]] 
 ![![41, 0, 0], ![0, 41, 0], ![12, 10, 1]] where
  M :=![![![1773105986839529704079233, -320601084919121793296749, 113664148727066581700576], ![-25006112719954647974126720, 4521436917551205616698036, -1603005424595608966483745], ![75533461226197724120110124, -13657451836807218013837567, 4842038002470327409994785]]]
  hmulB := by decide  
  f := ![![![-4006192587955, 76276905253, 119295379909]], ![![-26244983579980, -708940425159, 381384526265]], ![![-7855026080364, -228380528359, 108784694906]]]
  g := ![![![9978931758895871309081, -35542501760726527080549, 113664148727066581700576], ![-140732868897740009178580, 501255882036763299549646, -1603005424595608966483745], ![425097687720824273174944, -1514093460036841271067937, 4842038002470327409994785]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [6, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 40], [0, 1]]
 g := ![![[32, 37], [39], [21], [32, 5], [1]], ![[21, 4], [39], [21], [15, 36], [1]]]
 h' := ![![[13, 40], [16, 18], [2, 11], [13, 12], [35, 13], [0, 1]], ![[0, 1], [4, 23], [22, 30], [5, 29], [40, 28], [13, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [36, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [6, 28, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-945, -1751, 1510]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-465, -411, 1510]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4006192587955, -76276905253, -119295379909]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![4006192587955, -76276905253, -119295379909]] 
 ![![41, 0, 0], ![32, 1, 0], ![2, 0, 1]] where
  M :=![![![4006192587955, -76276905253, -119295379909], ![26244983579980, 708940425159, -381384526265], ![11531922439664, 3189520274165, 785217330412]]]
  hmulB := by decide  
  f := ![![![-1773105986839529704079233, 320601084919121793296749, -113664148727066581700576]], ![![-773982411192934208692896, 139946287801480287043852, -49615788650500527998407]], ![![-1928772517070165451908990, 348747658698669795132465, -123643080485962453009657]]]
  g := ![![![163064495509, -76276905253, -119295379909], ![105406317742, 708940425159, -381384526265], ![-2246418560840, 3189520274165, 785217330412]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1773105986839529704079233, -320601084919121793296749, 113664148727066581700576]] ![![4006192587955, -76276905253, -119295379909]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8355, 350, 312]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-8355, 350, 312]] 
 ![![43, 0, 0], ![0, 43, 0], ![34, 24, 1]] where
  M :=![![![-8355, 350, 312], ![-68640, 419, 1750], ![-63272, -4278, 69]]]
  hmulB := by decide  
  f := ![![![-174777, 31602, -11204]], ![![2464880, -445683, 158010]], ![![1064402, -192458, 68233]]]
  g := ![![![-441, -166, 312], ![-2980, -967, 1750], ![-1526, -138, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 42], [0, 1]]
 g := ![![[37, 36], [13, 16], [14], [32, 21], [1]], ![[24, 7], [12, 27], [14], [28, 22], [1]]]
 h' := ![![[8, 42], [40, 6], [34, 4], [29, 10], [13, 8], [0, 1]], ![[0, 1], [2, 37], [23, 39], [23, 33], [34, 35], [8, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [6, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 35, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1930, -44, 120]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, -68, 120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![174777, -31602, 11204]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![174777, -31602, 11204]] 
 ![![43, 0, 0], ![9, 1, 0], ![25, 0, 1]] where
  M :=![![![174777, -31602, 11204], ![-2464880, 445683, -158010], ![7445416, -1346230, 477285]]]
  hmulB := by decide  
  f := ![![![8355, -350, -312]], ![![3345, -83, -106]], ![![6329, -104, -183]]]
  g := ![![![4165, -31602, 11204], ![-58739, 445683, -158010], ![177427, -1346230, 477285]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-8355, 350, 312]] ![![174777, -31602, 11204]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-21, 20, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-21, 20, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![26, 20, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-21, 20, 1], ![-220, 26, 100], ![-4356, 496, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -20, 47]], ![![-1, 0, 1], ![-60, -42, 100], ![-96, 8, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [44, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 46], [0, 1]]
 g := ![![[16, 6], [8, 16], [31, 32], [7, 1], [1]], ![[22, 41], [24, 31], [16, 15], [8, 46], [1]]]
 h' := ![![[1, 46], [24, 10], [46, 4], [21, 19], [3, 1], [0, 1]], ![[0, 1], [34, 37], [3, 43], [40, 28], [4, 46], [1, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [29, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [44, 46, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4265, -4228, 2759]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1617, -1264, 2759]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-6, 1, 0]] 
 ![![47, 0, 0], ![41, 1, 0], ![41, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-6, 1, 0], ![0, -5, 5], ![-220, 27, -6]]]
  hmulB := by decide  
  f := ![![![73, -12, 0], ![564, 0, 0]], ![![67, -11, 0], ![518, 0, 0]], ![![67, -9, -2], ![518, 19, 0]]]
  g := ![![![1, 0, 0], ![-41, 47, 0], ![-41, 0, 47]], ![![-1, 1, 0], ![0, -5, 5], ![-23, 27, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-21, 20, 1]] ![![47, 0, 0], ![-6, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-282, 47, 0]], ![![-987, 940, 47], ![-94, -94, 94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-6, 1, 0]]], ![![![-21, 20, 1]], ![![-2, -2, 2]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-17, -13, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-17, -13, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![36, 40, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-17, -13, 1], ![-220, -3, -65], ![2904, -395, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -40, 53]], ![![-1, -1, 1], ![40, 49, -65], ![48, -15, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [27, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 52], [0, 1]]
 g := ![![[49, 4], [29], [29, 28], [52], [2, 1]], ![[4, 49], [29], [32, 25], [52], [4, 52]]]
 h' := ![![[2, 52], [50, 2], [12, 33], [28, 44], [52, 30], [0, 1]], ![[0, 1], [1, 51], [25, 20], [10, 9], [6, 23], [2, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [1, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [27, 51, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4329, -2690, 1748]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1269, -1370, 1748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![12, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![12, 1, 0]] 
 ![![53, 0, 0], ![12, 1, 0], ![43, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![12, 1, 0], ![0, 13, 5], ![-220, 27, 12]]]
  hmulB := by decide  
  f := ![![![205, 17, 0], ![-901, 0, 0]], ![![36, 3, 0], ![-158, 0, 0]], ![![155, 5, -3], ![-681, 32, 0]]]
  g := ![![![1, 0, 0], ![-12, 53, 0], ![-43, 0, 53]], ![![0, 1, 0], ![-7, 13, 5], ![-20, 27, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-17, -13, 1]] ![![53, 0, 0], ![12, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![636, 53, 0]], ![![-901, -689, 53], ![-424, -159, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![12, 1, 0]]], ![![![-17, -13, 1]], ![![-8, -3, -1]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [38, 27, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 21, 31], [52, 37, 28], [0, 1]]
 g := ![![[58, 18, 25], [43, 52, 35], [55, 26], [58, 33, 17], [1]], ![[33, 30, 45, 10], [10, 45, 37, 58], [19, 21], [41, 11, 19, 13], [58, 23, 3, 55]], ![[25, 3, 55, 46], [19, 33, 6, 25], [9, 48], [45, 19, 35, 12], [54, 49, 5, 4]]]
 h' := ![![[38, 21, 31], [18, 58, 54], [3, 36, 34], [38, 40, 12], [21, 32, 31], [0, 1]], ![[52, 37, 28], [17, 8, 20], [22, 16, 14], [6, 27, 32], [40, 32, 15], [38, 21, 31]], ![[0, 1], [55, 52, 44], [19, 7, 11], [40, 51, 15], [24, 54, 13], [52, 37, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 36], []]
 b := ![[], [9, 38, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [38, 27, 28, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3415412886, -999620480, 342921216]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57888354, -16942720, 5812224]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-33, -19, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-33, -19, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![28, 42, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-33, -19, 1], ![-220, -25, -95], ![4224, -557, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -42, 61]], ![![-1, -1, 1], ![40, 65, -95], ![72, -5, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [40, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 60], [0, 1]]
 g := ![![[], [14], [0, 60], [0, 14], [0, 1]], ![[], [14], [0, 1], [0, 47], [0, 60]]]
 h' := ![![[0, 60], [50], [0, 40], [0, 50], [0, 21], [0, 1]], ![[0, 1], [50], [0, 21], [0, 11], [0, 40], [0, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [0, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [40, 0, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3963, -1400, 1329]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-675, -938, 1329]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 1, 0]] 
 ![![61, 0, 0], ![34, 1, 0], ![6, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 1, 0], ![0, -26, 5], ![-220, 27, -27]]]
  hmulB := by decide  
  f := ![![![1567, -58, 0], ![3538, 0, 0]], ![![892, -33, 0], ![2014, 0, 0]], ![![186, 14, -4], ![420, 49, 0]]]
  g := ![![![1, 0, 0], ![-34, 61, 0], ![-6, 0, 61]], ![![-1, 1, 0], ![14, -26, 5], ![-16, 27, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-33, -19, 1]] ![![61, 0, 0], ![-27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1647, 61, 0]], ![![-2013, -1159, 61], ![671, 488, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-27, 1, 0]]], ![![![-33, -19, 1]], ![![11, 8, -2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [4, 27, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 47, 22], [51, 19, 45], [0, 1]]
 g := ![![[24, 59, 35], [11, 64, 62], [36, 65], [33, 10], [22, 1], []], ![[0, 23, 63, 22], [28, 3, 9, 29], [13, 15], [25, 55], [54, 26], [53, 15]], ![[61, 24, 20, 43], [24, 1, 1, 43], [59, 22], [12, 16], [49, 65], [30, 15]]]
 h' := ![![[38, 47, 22], [23, 66, 54], [63, 11, 14], [41, 65, 47], [46, 5, 55], [0, 0, 1], [0, 1]], ![[51, 19, 45], [49, 35, 66], [41, 37, 39], [48, 27, 45], [58, 53, 16], [26, 4, 19], [38, 47, 22]], ![[0, 1], [13, 33, 14], [49, 19, 14], [33, 42, 42], [9, 9, 63], [2, 63, 47], [51, 19, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 19], []]
 b := ![[], [0, 30, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [4, 27, 45, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18870416, -5588604, 2024740]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![281648, -83412, 30220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [58, 8, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 29, 3], [53, 41, 68], [0, 1]]
 g := ![![[35, 41, 15], [36, 44, 32], [3, 49, 50], [40, 60], [11, 1], []], ![[52, 62, 66, 16], [42, 64, 19, 27], [44, 55, 2, 49], [1, 36], [56, 48], [60, 9]], ![[70, 11, 63, 63], [46, 32, 53, 31], [22, 68, 3, 33], [3, 32], [57, 60], [66, 9]]]
 h' := ![![[29, 29, 3], [42, 30, 50], [39, 53, 48], [24, 26, 60], [1, 67, 42], [0, 0, 1], [0, 1]], ![[53, 41, 68], [28, 9, 10], [6, 26, 68], [58, 19, 53], [20, 44, 6], [59, 41, 41], [29, 29, 3]], ![[0, 1], [27, 32, 11], [15, 63, 26], [44, 26, 29], [17, 31, 23], [46, 30, 29], [53, 41, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 12], []]
 b := ![[], [3, 50, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [58, 8, 60, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-168924478, 47691552, -15282040]
  a := ![2, -8, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2379218, 671712, -215240]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![7, 25, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![7, 25, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![7, 25, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![7, 25, 1], ![-220, 59, 125], ![-5456, 631, 34]]]
  hmulB := by decide  
  f := ![![![-6, -25, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -25, 73]], ![![0, 0, 1], ![-15, -42, 125], ![-78, -3, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [69, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 72], [0, 1]]
 g := ![![[48, 18], [12], [41], [72, 24], [72], [1]], ![[0, 55], [12], [41], [8, 49], [72], [1]]]
 h' := ![![[46, 72], [36, 50], [34, 42], [69, 48], [12, 30], [4, 46], [0, 1]], ![[0, 1], [0, 23], [68, 31], [14, 25], [5, 43], [3, 27], [46, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [42, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [69, 27, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![633, -44, 80]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -28, 80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![21, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![21, 1, 0]] 
 ![![73, 0, 0], ![21, 1, 0], ![39, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![21, 1, 0], ![0, 22, 5], ![-220, 27, 21]]]
  hmulB := by decide  
  f := ![![![106, 5, 0], ![-365, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![48, -11, -3], ![-165, 44, 0]]]
  g := ![![![1, 0, 0], ![-21, 73, 0], ![-39, 0, 73]], ![![0, 1, 0], ![-9, 22, 5], ![-22, 27, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![7, 25, 1]] ![![73, 0, 0], ![21, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1533, 73, 0]], ![![511, 1825, 73], ![-73, 584, 146]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![21, 1, 0]]], ![![![7, 25, 1]], ![![-1, 8, 2]]]]
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
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![19, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![19, 1, 0]] 
 ![![79, 0, 0], ![19, 1, 0], ![3, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![19, 1, 0], ![0, 20, 5], ![-220, 27, 19]]]
  hmulB := by decide  
  f := ![![![438, 23, 0], ![-1817, 0, 0]], ![![76, 4, 0], ![-315, 0, 0]], ![![-18, -5, -1], ![75, 16, 0]]]
  g := ![![![1, 0, 0], ![-19, 79, 0], ![-3, 0, 79]], ![![0, 1, 0], ![-5, 20, 5], ![-10, 27, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![21, 1, 0]] 
 ![![79, 0, 0], ![21, 1, 0], ![34, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![21, 1, 0], ![0, 22, 5], ![-220, 27, 21]]]
  hmulB := by decide  
  f := ![![![1177, 56, 0], ![-4424, 0, 0]], ![![315, 15, 0], ![-1184, 0, 0]], ![![472, 18, -1], ![-1774, 16, 0]]]
  g := ![![![1, 0, 0], ![-21, 79, 0], ![-34, 0, 79]], ![![0, 1, 0], ![-8, 22, 5], ![-19, 27, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![38, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![38, 1, 0]] 
 ![![79, 0, 0], ![38, 1, 0], ![67, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![38, 1, 0], ![0, 39, 5], ![-220, 27, 38]]]
  hmulB := by decide  
  f := ![![![381, 10, 0], ![-790, 0, 0]], ![![190, 5, 0], ![-394, 0, 0]], ![![301, 0, -1], ![-624, 16, 0]]]
  g := ![![![1, 0, 0], ![-38, 79, 0], ![-67, 0, 79]], ![![0, 1, 0], ![-23, 39, 5], ![-48, 27, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![19, 1, 0]] ![![79, 0, 0], ![21, 1, 0]]
  ![![79, 0, 0], ![-15, 24, 1]] where
 M := ![![![6241, 0, 0], ![1659, 79, 0]], ![![1501, 79, 0], ![399, 41, 5]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![21, 1, 0], ![0, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![6, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-15, 24, 1]] ![![79, 0, 0], ![38, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![3002, 79, 0]], ![![-1185, 1896, 79], ![-790, 948, 158]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![38, 1, 0]]], ![![![-15, 24, 1]], ![![-10, 12, 2]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB254I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB254I1 : PrimesBelowBoundCertificateInterval O 31 79 254 where
  m := 11
  g := ![1, 2, 2, 2, 2, 1, 2, 1, 1, 2, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB254I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I43N1, I47N1, I53N1, I61N1, I73N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [I43N1], [I47N1], [I53N1], [], [I61N1], [], [], [I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
