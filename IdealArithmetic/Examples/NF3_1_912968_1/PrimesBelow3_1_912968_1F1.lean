
import IdealArithmetic.Examples.NF3_1_912968_1.RI3_1_912968_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [2, 22, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 36, 18], [20, 0, 19], [0, 1]]
 g := ![![[25, 9, 9], [8, 9], [20, 9, 26], [7, 1], []], ![[34, 22, 31, 13], [15, 30], [15, 10, 13, 29], [], [12, 28]], ![[10, 28, 6, 5], [20, 11], [29, 19, 24, 18], [11, 1], [11, 28]]]
 h' := ![![[24, 36, 18], [30, 9, 34], [34, 34, 3], [23, 29, 27], [0, 0, 1], [0, 1]], ![[20, 0, 19], [33, 22, 14], [27, 9, 20], [9, 25, 4], [34, 2], [24, 36, 18]], ![[0, 1], [1, 6, 26], [35, 31, 14], [5, 20, 6], [8, 35, 36], [20, 0, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 23], []]
 b := ![[], [33, 35, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [2, 22, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-210826, -38628, -6956]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5698, -1044, -188]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32620, -5387, 428]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![32620, -5387, 428]] 
 ![![41, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![32620, -5387, 428], ![75505, 43320, -10346], ![-972347, -88879, 37933]]]
  hmulB := by decide  
  f := ![![![723715426, 166304859, 37192942]], ![![193158203, 44386435, 9926722]], ![![863689345, 198469909, 44386435]]]
  g := ![![![927, -5387, 428], ![785, 43320, -10346], ![-21548, -88879, 37933]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48657785, -580848, 1112472]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-48657785, -580848, 1112472]] 
 ![![41, 0, 0], ![2, 1, 0], ![19, 0, 1]] where
  M :=![![![-48657785, -580848, 1112472], ![209676360, -20845985, -49224], ![9254232, 104513304, -21426833]]]
  hmulB := by decide  
  f := ![![![-451808002191601, -103822391233104, -23219166286872]], ![![-131606361556954, -30242242483649, -6763470276264]], ![![-748566701887619, -172015512364680, -38470090488953]]]
  g := ![![![-1673977, -580848, 1112472], ![6153746, -20845985, -49224], ![5057011, 104513304, -21426833]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56631883199, -9374816118, 3062426664]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-56631883199, -9374816118, 3062426664]] 
 ![![41, 0, 0], ![37, 1, 0], ![13, 0, 1]] where
  M :=![![![-56631883199, -9374816118, 3062426664], ![569423823378, 19928783401, -15687205572], ![-1444160593254, 93309250098, 10553967283]]]
  hmulB := by decide  
  f := ![![![-1674089116060634615539, -384694238091472880466, -86034229974462005232]], ![![-1916742951158738357177, -440454431092845885941, -98504615005182974628]], ![![-2528683710130342901705, -581074235481546439452, -129953270565406431581]]]
  g := ![![![6107921135, -9374816118, 3062426664], ![877866097, 19928783401, -15687205572], ![-122775717599, 93309250098, 10553967283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![32620, -5387, 428]] ![![-48657785, -580848, 1112472]]
  ![![-2712782686724, 138081753547, 27383321804]] where
 M := ![![![-2712782686724, 138081753547, 27383321804]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-2712782686724, 138081753547, 27383321804]] ![![-56631883199, -9374816118, 3062426664]]
  ![![41, 0, 0]] where
 M := ![![![192711118040564595461626, 30738757436923378827571, -10184812204675889034088]]]
 hmul := by decide  
 g := ![![![![4700271171721087694186, 749725791144472654331, -248410053772582659368]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12473436972504, -2866310572409, -641030716208]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-12473436972504, -2866310572409, -641030716208]] 
 ![![43, 0, 0], ![0, 43, 0], ![25, 13, 1]] where
  M :=![![![-12473436972504, -2866310572409, -641030716208], ![-124021115935721, -28499204877704, -6373651861026], ![-610322984819557, -140248050944481, -31365515450113]]]
  hmulB := by decide  
  f := ![![![-564722, 904283, -172214]], ![![-31644163, -4870072, 1636352]], ![![-6349060, -849388, 302359]]]
  g := ![![![82612347272, 127141598565, -641030716208], ![821399548603, 1264145798038, -6373651861026], ![4042207010076, 6221015114116, -31365515450113]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [12, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 42], [0, 1]]
 g := ![![[33, 9], [2, 31], [25], [3, 38], [1]], ![[38, 34], [24, 12], [25], [5, 5], [1]]]
 h' := ![![[34, 42], [19, 3], [7, 17], [7, 5], [31, 34], [0, 1]], ![[0, 1], [35, 40], [26, 26], [5, 38], [26, 9], [34, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [31, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [12, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1067, 2149, 678]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-419, -155, 678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-564722, 904283, -172214]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-564722, 904283, -172214]] 
 ![![43, 0, 0], ![16, 1, 0], ![23, 0, 1]] where
  M :=![![![-564722, 904283, -172214], ![-31644163, -4870072, 1636352], ![152482589, 4180177, -3965789]]]
  hmulB := by decide  
  f := ![![![-12473436972504, -2866310572409, -641030716208]], ![![-7525490871995, -1729306372936, -386747519078]], ![![-20865396167143, -4794725444416, -1072307486579]]]
  g := ![![![-257496, 904283, -172214], ![200951, -4870072, 1636352], ![4111928, 4180177, -3965789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-12473436972504, -2866310572409, -641030716208]] ![![-564722, 904283, -172214]]
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
 ![![47, 0, 0], ![22, 1, 0], ![17, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![22, 1, 0], ![1, 22, 2], ![189, 25, 23]]]
  hmulB := by decide  
  f := ![![![252, 8903, 810], ![329, -19035, 0]], ![![101, 4154, 378], ![189, -8883, 0]], ![![86, 3220, 293], ![130, -6885, 0]]]
  g := ![![![1, 0, 0], ![-22, 47, 0], ![-17, 0, 47]], ![![0, 1, 0], ![-11, 22, 2], ![-16, 25, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-14, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-14, 1, 0]] 
 ![![47, 0, 0], ![33, 1, 0], ![20, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-14, 1, 0], ![1, -14, 2], ![189, 25, -13]]]
  hmulB := by decide  
  f := ![![![-5, 279, -40], ![47, 940, 0]], ![![1, 195, -28], ![48, 658, 0]], ![![-6, 119, -17], ![7, 400, 0]]]
  g := ![![![1, 0, 0], ![-33, 47, 0], ![-20, 0, 47]], ![![-1, 1, 0], ![9, -14, 2], ![-8, 25, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-9, 1, 0]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-9, 1, 0]] 
 ![![47, 0, 0], ![38, 1, 0], ![7, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-9, 1, 0], ![1, -9, 2], ![189, 25, -8]]]
  hmulB := by decide  
  f := ![![![-1036, 10053, -2236], ![423, 52546, 0]], ![![-830, 8119, -1806], ![377, 42441, 0]], ![![-152, 1497, -333], ![75, 7826, 0]]]
  g := ![![![1, 0, 0], ![-38, 47, 0], ![-7, 0, 47]], ![![-1, 1, 0], ![7, -9, 2], ![-15, 25, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![22, 1, 0]] ![![47, 0, 0], ![-14, 1, 0]]
  ![![47, 0, 0], ![-36, 4, 1]] where
 M := ![![![2209, 0, 0], ![-658, 47, 0]], ![![1034, 47, 0], ![-307, 8, 2]]]
 hmul := by decide  
 g := ![![![![47, 0, 0], ![0, 0, 0]], ![![22, -3, -1], ![47, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![31, -4, -1], ![49, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-36, 4, 1]] ![![47, 0, 0], ![-9, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-423, 47, 0]], ![![-1692, 188, 47], ![517, -47, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-9, 1, 0]]], ![![![-36, 4, 1]], ![![11, -1, 0]]]]
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
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [11, 44, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 38, 15], [29, 14, 38], [0, 1]]
 g := ![![[36, 11, 17], [18, 10], [50, 12, 11], [30, 16], [1]], ![[20, 40, 19, 11], [40, 36], [17, 47, 14, 1], [24, 17], [34, 25, 36, 36]], ![[7, 32, 31, 13], [50, 49], [21, 14, 12, 29], [32, 24], [36, 8, 31, 17]]]
 h' := ![![[28, 38, 15], [43, 10, 21], [33, 9, 40], [3, 2, 45], [42, 9, 4], [0, 1]], ![[29, 14, 38], [22, 21, 20], [12, 9, 6], [50, 26, 24], [7, 49, 32], [28, 38, 15]], ![[0, 1], [23, 22, 12], [19, 35, 7], [10, 25, 37], [37, 48, 17], [29, 14, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 35], []]
 b := ![[], [15, 49, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [11, 44, 49, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6584458445, -1596141428, -254395442]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-124235065, -30115876, -4799914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [5, 32, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 52, 34], [15, 6, 25], [0, 1]]
 g := ![![[54, 19, 17], [55, 30, 57], [38, 49], [1, 21, 7], [1]], ![[0, 37, 44, 40], [53, 35, 18, 40], [26, 41], [27, 55, 10, 54], [23, 39, 19, 10]], ![[57, 45, 10, 5], [34, 8, 44, 3], [5, 53], [57, 23, 46, 17], [7, 48, 53, 49]]]
 h' := ![![[25, 52, 34], [20, 4, 28], [12, 13, 36], [54, 6, 7], [54, 27, 40], [0, 1]], ![[15, 6, 25], [6, 6, 9], [5, 37, 9], [28, 55, 10], [52, 45, 37], [25, 52, 34]], ![[0, 1], [14, 49, 22], [21, 9, 14], [39, 57, 42], [36, 46, 41], [15, 6, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 47], []]
 b := ![[], [57, 9, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [5, 32, 19, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2492455, -585516, -79532]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42245, -9924, -1348]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [9, 4, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 26, 40], [30, 34, 21], [0, 1]]
 g := ![![[42, 7, 15], [0, 41], [18, 42, 42], [8, 15, 19], [1]], ![[1, 33, 46, 8], [4, 25], [28, 10, 50, 33], [13, 44, 29, 51], [32, 31, 9, 11]], ![[21, 14, 16, 33], [59, 52], [39, 2], [56, 31, 54, 33], [19, 14, 10, 50]]]
 h' := ![![[49, 26, 40], [14, 26, 36], [21, 37, 23], [50, 36, 46], [52, 57, 18], [0, 1]], ![[30, 34, 21], [45, 25, 7], [52, 53, 5], [19, 33, 15], [58, 28, 25], [49, 26, 40]], ![[0, 1], [54, 10, 18], [55, 32, 33], [15, 53], [50, 37, 18], [30, 34, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 47], []]
 b := ![[], [3, 44, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [9, 4, 43, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-195383, -31720, -5490]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3203, -520, -90]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-49, -20, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-49, -20, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![18, 47, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-49, -20, 1], ![169, -24, -39], ![-3673, -393, -44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -47, 67]], ![![-1, -1, 1], ![13, 27, -39], ![-43, 25, -44]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [3, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 66], [0, 1]]
 g := ![![[31, 22], [], [], [], [6], [1]], ![[62, 45], [], [], [], [6], [1]]]
 h' := ![![[41, 66], [0, 25], [62], [14], [58], [64, 41], [0, 1]], ![[0, 1], [20, 42], [62], [14], [58], [3, 26], [41, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [49, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [3, 26, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22929, 4383, 1151]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33, -742, 1151]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 1, 0]] 
 ![![67, 0, 0], ![39, 1, 0], ![44, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 1, 0], ![1, -28, 2], ![189, 25, -27]]]
  hmulB := by decide  
  f := ![![![1803, -70814, 5060], ![-1742, -169510, 0]], ![![1053, -41201, 2944], ![-1004, -98624, 0]], ![![1192, -46505, 3323], ![-1125, -111320, 0]]]
  g := ![![![1, 0, 0], ![-39, 67, 0], ![-44, 0, 67]], ![![-1, 1, 0], ![15, -28, 2], ![6, 25, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-49, -20, 1]] ![![67, 0, 0], ![-28, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1876, 67, 0]], ![![-3283, -1340, 67], ![1541, 536, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-28, 1, 0]]], ![![![-49, -20, 1]], ![![23, 8, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-640, 25, 8]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-640, 25, 8]] 
 ![![71, 0, 0], ![0, 71, 0], ![62, 12, 1]] where
  M :=![![![-640, 25, 8], ![1537, -440, 58], ![5581, 1481, -415]]]
  hmulB := by decide  
  f := ![![![1362, 313, 70]], ![![13543, 3112, 696]], ![![4417, 1015, 227]]]
  g := ![![![-16, -1, 8], ![-29, -16, 58], ![441, 91, -415]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [9, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 70], [0, 1]]
 g := ![![[0, 8], [0, 50], [], [], [], [1]], ![[0, 63], [0, 21], [], [], [], [1]]]
 h' := ![![[0, 70], [0, 47], [0, 60], [29], [10], [62], [0, 1]], ![[0, 1], [0, 24], [0, 11], [29], [10], [62], [0, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [9, 0, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2417, 501, 237]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-241, -33, 237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1362, 313, 70]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1362, 313, 70]] 
 ![![71, 0, 0], ![46, 1, 0], ![43, 0, 1]] where
  M :=![![![1362, 313, 70], ![13543, 3112, 696], ![66647, 15315, 3425]]]
  hmulB := by decide  
  f := ![![![-640, 25, 8]], ![![-393, 10, 6]], ![![-309, 36, -1]]]
  g := ![![![-226, 313, 70], ![-2247, 3112, 696], ![-11058, 15315, 3425]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-640, 25, 8]] ![![1362, 313, 70]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-51, -8, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-51, -8, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![22, 65, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-51, -8, 1], ![181, -26, -15], ![-1405, -93, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -65, 73]], ![![-1, -1, 1], ![7, 13, -15], ![-9, 29, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [55, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 72], [0, 1]]
 g := ![![[36, 4], [18], [36], [3, 12], [8], [1]], ![[0, 69], [18], [36], [41, 61], [8], [1]]]
 h' := ![![[64, 72], [55, 71], [60, 50], [54, 67], [30, 42], [18, 64], [0, 1]], ![[0, 1], [0, 2], [48, 23], [35, 6], [17, 31], [26, 9], [64, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [30, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [55, 9, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3302, 1925, 462]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94, -385, 462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![15, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![15, 1, 0]] 
 ![![73, 0, 0], ![15, 1, 0], ![34, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![15, 1, 0], ![1, 15, 2], ![189, 25, 16]]]
  hmulB := by decide  
  f := ![![![-2519, -40936, -5460], ![-1022, 199290, 0]], ![![-515, -8397, -1120], ![-218, 40880, 0]], ![![-1172, -19066, -2543], ![-482, 92820, 0]]]
  g := ![![![1, 0, 0], ![-15, 73, 0], ![-34, 0, 73]], ![![0, 1, 0], ![-4, 15, 2], ![-10, 25, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-51, -8, 1]] ![![73, 0, 0], ![15, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1095, 73, 0]], ![![-3723, -584, 73], ![-584, -146, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![15, 1, 0]]], ![![![-51, -8, 1]], ![![-8, -2, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-33, -21, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-33, -21, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![46, 58, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-33, -21, 1], ![168, -8, -41], ![-3862, -418, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -58, 79]], ![![-1, -1, 1], ![26, 30, -41], ![-32, 16, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [30, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 78], [0, 1]]
 g := ![![[53, 13], [38, 5], [31, 55], [52, 25], [21], [1]], ![[2, 66], [67, 74], [34, 24], [39, 54], [21], [1]]]
 h' := ![![[69, 78], [45, 31], [18, 20], [20, 56], [33, 74], [49, 69], [0, 1]], ![[0, 1], [51, 48], [55, 59], [13, 23], [4, 5], [70, 10], [69, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [40, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [30, 10, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2680, 2675, 625]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-330, -425, 625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-38, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-38, 1, 0]] 
 ![![79, 0, 0], ![41, 1, 0], ![29, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-38, 1, 0], ![1, -38, 2], ![189, 25, -37]]]
  hmulB := by decide  
  f := ![![![-1027, 63595, -3348], ![1343, 132246, 0]], ![![-525, 32975, -1736], ![712, 68572, 0]], ![![-377, 23345, -1229], ![493, 48546, 0]]]
  g := ![![![1, 0, 0], ![-41, 79, 0], ![-29, 0, 79]], ![![-1, 1, 0], ![19, -38, 2], ![3, 25, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-33, -21, 1]] ![![79, 0, 0], ![-38, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-3002, 79, 0]], ![![-2607, -1659, 79], ![1422, 790, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-38, 1, 0]]], ![![![-33, -21, 1]], ![![18, 10, -1]]]]
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


lemma PB271I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB271I1 : PrimesBelowBoundCertificateInterval O 31 79 271 where
  m := 11
  g := ![1, 3, 2, 3, 1, 1, 1, 2, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB271I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
    · exact ![50653]
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![6241, 79]
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
      exact NI41N2
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
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N0, I41N1, I41N2, I43N1, I47N0, I47N1, I47N2, I67N1, I71N1, I73N1, I79N1]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N1], [I47N0, I47N1, I47N2], [], [], [], [I67N1], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
