
import IdealArithmetic.Examples.NF3_1_401464_1.RI3_1_401464_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-743, -152, -4]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-743, -152, -4]] 
 ![![37, 0, 0], ![0, 37, 0], ![10, 1, 1]] where
  M :=![![![-743, -152, -4], ![324, -715, -308], ![18340, 1316, -867]]]
  hmulB := by decide  
  f := ![![![27709, -3704, 1188]], ![![-145076, 19393, -6220]], ![![13458, -1799, 577]]]
  g := ![![![-19, -4, -4], ![92, -11, -308], ![730, 59, -867]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [9, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 36], [0, 1]]
 g := ![![[33, 33], [30], [13, 30], [1], [1]], ![[0, 4], [30], [20, 7], [1], [1]]]
 h' := ![![[36, 36], [25, 25], [31, 17], [35, 17], [28, 36], [0, 1]], ![[0, 1], [0, 12], [14, 20], [18, 20], [29, 1], [36, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [18, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [9, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-718, -279, -20]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, -7, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27709, 3704, -1188]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-27709, 3704, -1188]] 
 ![![37, 0, 0], ![34, 1, 0], ![33, 0, 1]] where
  M :=![![![-27709, 3704, -1188], ![145076, -19393, 6220], ![-365932, 48916, -15689]]]
  hmulB := by decide  
  f := ![![![743, 152, 4]], ![![674, 159, 12]], ![![167, 100, 27]]]
  g := ![![![-3093, 3704, -1188], ![16194, -19393, 6220], ![-40847, 48916, -15689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-743, -152, -4]] ![![-27709, 3704, -1188]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1065394527612055639151266181, -142416554951978805171330300, 45677847634154620052623972]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1065394527612055639151266181, -142416554951978805171330300, 45677847634154620052623972]] 
 ![![41, 0, 0], ![3, 1, 0], ![37, 0, 1]] where
  M :=![![![1065394527612055639151266181, -142416554951978805171330300, 45677847634154620052623972], ![-5578080423416378591433582968, 745649594172973298782898377, -239155262269802990290036628], ![14069865638333736752072995464, -1880788516287889427115998136, 603233039220994493611568077]]]
  hmulB := by decide  
  f := ![![![-161042311414379, -10619558083092, 7984216134956]], ![![-35216297863073, -6068060941667, 260920692040]], ![![-126776676266983, -20038838024268, 1655234501249]]]
  g := ![![![-4815516341359241153215363, -142416554951978805171330300, 45677847634154620052623972], ![25212573123107613486562857, 745649594172973298782898377, -239155262269802990290036628], ![-63594908877546127566025097, -1880788516287889427115998136, 603233039220994493611568077]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-660174727, -105968464, 7977754]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-660174727, -105968464, 7977754]] 
 ![![41, 0, 0], ![13, 1, 0], ![39, 0, 1]] where
  M :=![![![-660174727, -105968464, 7977754], ![-1055321190, -716019005, -203959174], ![12107648714, 239180746, -821987469]]]
  hmulB := by decide  
  f := ![![![637341757066712149, -85196624364053132, 27325463868703506]], ![![120695512612865551, -16133966018217149, 5174713303262020]], ![![811542014663311601, -108482834228732222, 34794145768321249]]]
  g := ![![![9909339, -105968464, 7977754], ![395300821, -716019005, -203959174], ![1001361227, 239180746, -821987469]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![96801, -2240, -8218]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![96801, -2240, -8218]] 
 ![![41, 0, 0], ![24, 1, 0], ![20, 0, 1]] where
  M :=![![![96801, -2240, -8218], ![975702, 154327, -12698], ![784294, 533414, 152087]]]
  hmulB := by decide  
  f := ![![![30244421421, -4042921372, 1296702806]], ![![13841842898, -1850307589, 593456766]], ![![24495214510, -3274396454, 1050210647]]]
  g := ![![![7681, -2240, -8218], ![-60346, 154327, -12698], ![-367302, 533414, 152087]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1065394527612055639151266181, -142416554951978805171330300, 45677847634154620052623972]] ![![-660174727, -105968464, 7977754]]
  ![![30244421421, -4042921372, 1296702806]] where
 M := ![![![30244421421, -4042921372, 1296702806]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![30244421421, -4042921372, 1296702806]] ![![96801, -2240, -8218]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93645463931653390190, -12518052246728051521, 4014966401871147200]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![93645463931653390190, -12518052246728051521, 4014966401871147200]] 
 ![![43, 0, 0], ![0, 43, 0], ![9, 38, 1]] where
  M :=![![![93645463931653390190, -12518052246728051521, 4014966401871147200], ![-490299054069394568321, 65540699118555359790, -21021138091584955842], ![1236705334042755857399, -165316517590785912953, 53022646871827308269]]]
  hmulB := by decide  
  f := ![![![-6921481812, -299264057, 405461574]], ![![-48549191363, -9759712830, -193066540]], ![![-44118471267, -9232830112, -319682587]]]
  g := ![![![1337459681739838730, -3839227337623991747, 4014966401871147200], ![-7002530494072789901, 20101022013925201902, -21021138091584955842], ![17662825865030467046, -50701792993493572725, 53022646871827308269]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [6, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 42], [0, 1]]
 g := ![![[19, 36], [28, 1], [1], [13, 10], [1]], ![[0, 7], [0, 42], [1], [34, 33], [1]]]
 h' := ![![[15, 42], [4, 37], [15, 42], [8, 42], [37, 15], [0, 1]], ![[0, 1], [0, 6], [0, 1], [36, 1], [4, 28], [15, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [2, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [6, 28, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![875, -1499, -27]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, -11, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6921481812, 299264057, -405461574]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![6921481812, 299264057, -405461574]] 
 ![![43, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  M :=![![![6921481812, 299264057, -405461574], ![48549191363, 9759712830, 193066540], ![-10068343621, 23449230763, 10058976887]]]
  hmulB := by decide  
  f := ![![![-93645463931653390190, 12518052246728051521, -4014966401871147200]], ![![-8197909798034556823, 1095855141906909393, -351478128494310906]], ![![-35293993624132930883, 4717922658859769012, -1513198745986994183]]]
  g := ![![![126616047, 299264057, -405461574], ![-927149389, 9759712830, 193066540], ![-5843915143, 23449230763, 10058976887]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![93645463931653390190, -12518052246728051521, 4014966401871147200]] ![![6921481812, 299264057, -405461574]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7899513424, 1055967023, -338684648]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-7899513424, 1055967023, -338684648]] 
 ![![47, 0, 0], ![0, 47, 0], ![5, 28, 1]] where
  M :=![![![-7899513424, 1055967023, -338684648], ![41359440135, -5528720888, 1773249398], ![-104322942913, 13945363663, -4472753865]]]
  hmulB := by decide  
  f := ![![![-51218, -13793, -1590]], ![![175417, -40088, -29176]], ![![136109, -21164, -18697]]]
  g := ![![![-132044472, 224236961, -338684648], ![691344535, -1174036256, 1773249398], ![-1743812204, 2961329189, -4472753865]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [12, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 46], [0, 1]]
 g := ![![[7, 4], [33, 28], [38, 27], [8, 6], [1]], ![[0, 43], [31, 19], [26, 20], [21, 41], [1]]]
 h' := ![![[10, 46], [27, 2], [14, 13], [45, 11], [35, 10], [0, 1]], ![[0, 1], [0, 45], [3, 34], [14, 36], [41, 37], [10, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [2, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [12, 37, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-256887, -273597, -24484]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2861, 8765, -24484]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51218, 13793, 1590]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![51218, 13793, 1590]] 
 ![![47, 0, 0], ![37, 1, 0], ![21, 0, 1]] where
  M :=![![![51218, 13793, 1590], ![-175417, 40088, 29176], ![-1741537, -196721, 53881]]]
  hmulB := by decide  
  f := ![![![7899513424, -1055967023, 338684648]], ![![5338777799, -713660829, 228895374]], ![![5749206911, -768524918, 246492159]]]
  g := ![![![-10479, 13793, 1590], ![-48327, 40088, 29176], ![93737, -196721, 53881]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-7899513424, 1055967023, -338684648]] ![![51218, 13793, 1590]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [10, 17, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 16, 9], [31, 36, 44], [0, 1]]
 g := ![![[39, 11, 24], [3, 36], [8, 10, 17], [48, 38], [1]], ![[15, 11, 28, 38], [8, 10], [19, 23, 11, 49], [20, 37], [20, 24, 22, 40]], ![[26, 42, 25, 6], [11, 49], [35, 45, 42, 44], [20, 40], [33, 39, 0, 13]]]
 h' := ![![[34, 16, 9], [10, 9, 17], [26, 4, 6], [44, 45, 32], [43, 36, 12], [0, 1]], ![[31, 36, 44], [13, 17, 4], [27, 41, 40], [6, 32, 20], [43, 0, 14], [34, 16, 9]], ![[0, 1], [24, 27, 32], [44, 8, 7], [8, 29, 1], [46, 17, 27], [31, 36, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 47], []]
 b := ![[], [43, 3, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [10, 17, 41, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-946156, -162233, -5883]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17852, -3061, -111]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2424916, 438573, -9744]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![2424916, 438573, -9744]] 
 ![![59, 0, 0], ![0, 59, 0], ![31, 43, 1]] where
  M :=![![![2424916, 438573, -9744], ![1598109, 2493124, 867402], ![-51576315, -2456139, 2931697]]]
  hmulB := by decide  
  f := ![![![159992271734, -21386958135, 6859527078]], ![![-837670680417, 111975582188, -35914389192]], ![![-490630186814, 65584963270, -21035335115]]]
  g := ![![![46220, 14535, -9744], ![-428667, -589918, 867402], ![-2414558, -2178290, 2931697]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [11, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 58], [0, 1]]
 g := ![![[42, 22], [45, 9], [16], [40, 15], [10, 1]], ![[26, 37], [17, 50], [16], [13, 44], [20, 58]]]
 h' := ![![[10, 58], [36, 9], [22, 3], [32, 4], [8, 30], [0, 1]], ![[0, 1], [8, 50], [52, 56], [13, 55], [13, 29], [10, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [36, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [11, 49, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-764, -327, -116]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 79, -116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159992271734, 21386958135, -6859527078]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-159992271734, 21386958135, -6859527078]] 
 ![![59, 0, 0], ![31, 1, 0], ![51, 0, 1]] where
  M :=![![![-159992271734, 21386958135, -6859527078], ![837670680417, -111975582188, 35914389192], ![-2112897812151, 282441498969, -90588624053]]]
  hmulB := by decide  
  f := ![![![-2424916, -438573, 9744]], ![![-1301195, -272693, -9582]], ![![-1221939, -337476, -41267]]]
  g := ![![![-8019526999, 21386958135, -6859527078], ![41987794567, -111975582188, 35914389192], ![-105907872093, 282441498969, -90588624053]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![2424916, 438573, -9744]] ![![-159992271734, 21386958135, -6859527078]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189219341784997, -19086369567892, 6761112668778]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-189219341784997, -19086369567892, 6761112668778]] 
 ![![61, 0, 0], ![0, 61, 0], ![35, 57, 1]] where
  M :=![![![-189219341784997, -19086369567892, 6761112668778], ![-823658777152474, -236547130466443, -31411626467006], ![1845327880446134, -292345511157770, -255633500034335]]]
  hmulB := by decide  
  f := ![![![-840759391613467153234422685, 112388465487511950531552080, -36046814951436137746193246]], ![![4401959444708412342328548354, -588431686953414189011069963, 188730116023587763316910914]], ![![3448882485095650946135703921, -461029176733668811159628773, 147867784730792384417502305]]]
  g := ![![![-6981283363807, -6630652322758, 6761112668778], ![4520461462176, 25474025871359, -31411626467006], ![176926235764719, 234078098209825, -255633500034335]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [12, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 60], [0, 1]]
 g := ![![[27, 56], [22], [3, 47], [55, 45], [42, 1]], ![[0, 5], [22], [25, 14], [54, 16], [23, 60]]]
 h' := ![![[42, 60], [56, 19], [25, 49], [11, 13], [45, 44], [0, 1]], ![[0, 1], [0, 42], [9, 12], [8, 48], [2, 17], [42, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [51, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [12, 19, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13718, -928, 842]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-708, -802, 842]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-840759391613467153234422685, 112388465487511950531552080, -36046814951436137746193246]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-840759391613467153234422685, 112388465487511950531552080, -36046814951436137746193246]] 
 ![![61, 0, 0], ![7, 1, 0], ![37, 0, 1]] where
  M :=![![![-840759391613467153234422685, 112388465487511950531552080, -36046814951436137746193246], ![4401959444708412342328548354, -588431686953414189011069963, 188730116023587763316910914], ![-11103278051073445435244523022, 1484230083527893024289309938, -476043221465902238479517883]]]
  hmulB := by decide  
  f := ![![![-189219341784997, -19086369567892, 6761112668778]], ![![-35216297863073, -6068060941667, 260920692040]], ![![-84521110911455, -16369527625734, -89710349009]]]
  g := ![![![-4815516341359241153215363, 112388465487511950531552080, -36046814951436137746193246], ![25212573123107613486562857, -588431686953414189011069963, 188730116023587763316910914], ![-63594908877546127566025097, 1484230083527893024289309938, -476043221465902238479517883]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-189219341784997, -19086369567892, 6761112668778]] ![![-840759391613467153234422685, 112388465487511950531552080, -36046814951436137746193246]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-74, 1, 6]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-74, 1, 6]] 
 ![![67, 0, 0], ![2, 1, 0], ![32, 0, 1]] where
  M :=![![![-74, 1, 6], ![-713, -116, 8], ![-497, -385, -115]]]
  hmulB := by decide  
  f := ![![![16420, -2195, 704]], ![![-793, 106, -34]], ![![11079, -1481, 475]]]
  g := ![![![-4, 1, 6], ![-11, -116, 8], ![59, -385, -115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1717900815658812467, -1234333039244327622, -359276127017819020]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-1717900815658812467, -1234333039244327622, -359276127017819020]] 
 ![![67, 0, 0], ![32, 1, 0], ![58, 0, 1]] where
  M :=![![![-1717900815658812467, -1234333039244327622, -359276127017819020], ![41519526075876135758, 797032073465920673, -2827942205506474264], ![169520027672197585278, 31274727276832891614, -437300965778406949]]]
  hmulB := by decide  
  f := ![![![88094578336377284097277731289646465419, -11776037919712803871133959370125143558, 3776977093793931083025644639317920668]], ![![35190898428102723706891070594324316274, -4704141414193879960599828075068411539, 1508778630683195791008632154585687984]], ![![93625141776816245971290059217423254860, -12515335683796576950126082688856885426, 4014095107464999484484352963055750387]]]
  g := ![![![874907041898405591, -1234333039244327622, -359276127017819020], ![2687091755885704202, 797032073465920673, -2827942205506474264], ![-12028474465243393184, 31274727276832891614, -437300965778406949]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-74, 1, 6]] ![![-1717900815658812467, -1234333039244327622, -359276127017819020]]
  ![![1185764352467813769984, 279786040638543514385, 21134685399141691522]] where
 M := ![![![1185764352467813769984, 279786040638543514385, 21134685399141691522]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![1185764352467813769984, 279786040638543514385, 21134685399141691522]] ![![-1717900815658812467, -1234333039244327622, -359276127017819020]]
  ![![67, 0, 0]] where
 M := ![![![13162310715380236589817459898871720901418, -579648146972401514494586345529552620435, -1226477795280182423071201580343075769698]]]
 hmul := by decide  
 g := ![![![![196452398737018456564439699983160013454, -8651464880185097231262482769097800305, -18305638735525110792107486273777250294]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1482879547281491393881361306588630107, -198223842022098121410213189683109038, 63577148431902347751339505171856492]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1482879547281491393881361306588630107, -198223842022098121410213189683109038, 63577148431902347751339505171856492]] 
 ![![71, 0, 0], ![0, 71, 0], ![22, 38, 1]] where
  M :=![![![1482879547281491393881361306588630107, -198223842022098121410213189683109038, 63577148431902347751339505171856492], ![-7763904505418477503819614305134031586, 1037839508258174959621984770385634663, -332870535612293895069086874194361584], ![19583276849419828539480980746463016526, -2617793457055161058462896498045195730, 839615666236076838211771580702525625]]]
  hmulB := by decide  
  f := ![![![959858617703843705, 70922027088069290, -44564700460653324]], ![![5374121381905814846, 1271811520928416973, 97279353715485256]], ![![3094385309964034360, 735214708882000616, 57167965902402153]]]
  g := ![![![1185665940558306244392847786025173, -36819091301892779379734005439628954, 63577148431902347751339505171856492], ![-6207784816169180454925395392367278, 192773519176413281299257549151709505, -332870535612293895069086874194361584], ![15658199890508987307352196774752856, -486242095408818040993101641756917880, 839615666236076838211771580702525625]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [63, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 70], [0, 1]]
 g := ![![[5, 58], [33, 9], [29, 4], [48], [38], [1]], ![[53, 13], [38, 62], [47, 67], [48], [38], [1]]]
 h' := ![![[40, 70], [51, 49], [19, 68], [56, 2], [13, 30], [8, 40], [0, 1]], ![[0, 1], [23, 22], [41, 3], [65, 69], [6, 41], [46, 31], [40, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [31, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [63, 31, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1589, -360, -144]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![67, 72, -144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-959858617703843705, -70922027088069290, 44564700460653324]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-959858617703843705, -70922027088069290, 44564700460653324]] 
 ![![71, 0, 0], ![65, 1, 0], ![18, 0, 1]] where
  M :=![![![-959858617703843705, -70922027088069290, 44564700460653324], ![-5374121381905814846, -1271811520928416973, -97279353715485256], ![5632145094459086098, -2311121939404674382, -1342733548016486263]]]
  hmulB := by decide  
  f := ![![![-1482879547281491393881361306588630107, 198223842022098121410213189683109038, -63577148431902347751339505171856492]], ![![-1248215015040541733781251698917280639, 166855073565890182141434824774879617, -53516114260019136743210999464455076]], ![![-651762094373051741258387102324765612, 87124262161308834420376533976636034, -27943723070567874615998347518252711]]]
  g := ![![![40111387813083103, -70922027088069290, 44564700460653324], ![1113305011905915817, -1271811520928416973, -97279353715485256], ![2535553169296615122, -2311121939404674382, -1342733548016486263]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1482879547281491393881361306588630107, -198223842022098121410213189683109038, 63577148431902347751339505171856492]] ![![-959858617703843705, -70922027088069290, 44564700460653324]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [17, 46, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 64], [17, 8], [0, 1]]
 g := ![![[64, 23, 36], [50, 54], [10, 9], [1, 11, 69], [24, 1], []], ![[18, 2, 69], [63, 25], [0, 65], [28, 40, 41], [31, 64], []], ![[55, 48, 41], [19, 67], [17, 72], [54, 22, 36], [41, 8], []]]
 h' := ![![[7, 64], [25, 64, 67], [46, 69, 28], [56, 10, 70], [30, 47, 19], [0, 0, 1], [0, 1]], ![[17, 8], [33, 34, 25], [3, 12, 5], [52, 69, 49], [49, 30, 6], [49, 20, 8], [7, 64]], ![[0, 1], [36, 48, 54], [40, 65, 40], [16, 67, 27], [42, 69, 48], [70, 53, 64], [17, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69], []]
 b := ![[], [62, 21, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [17, 46, 49, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![435810, -4015, -16060]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5970, -55, -220]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12599315601864976890641539667874459574, -1684212820946371766093778070324985225, 540184507655155763157541848219566276]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![12599315601864976890641539667874459574, -1684212820946371766093778070324985225, 540184507655155763157541848219566276]] 
 ![![79, 0, 0], ![0, 79, 0], ![49, 17, 1]] where
  M :=![![![12599315601864976890641539667874459574, -1684212820946371766093778070324985225, 540184507655155763157541848219566276], ![-65966169231909907581841258008453372069, 8818024048278886548538746730337495642, -2828241134237587769030014292430404174], ![166389701710343427086234453930840566387, -22242134235650210716268689945557778813, 7133811227332514782444968660012510417]]]
  hmulB := by decide  
  f := ![![![-524230478659074212, -454009636330614197, -140299135189263798]], ![![16241587451191777765, 457863467665772374, -1048318407850492192]], ![![3965641588053573346, -30960509603089198, -312559705397432091]]]
  g := ![![![-175566142699210829165544441707396050, -137561385456759743541417588481741923, 540184507655155763157541848219566276], ![919210713237112570894043573678942183, 720229409244530109139860629134865400, -2828241134237587769030014292430404174], ![-2318570233277845534855303929237625874, -1816669937978518506554850090705955138, 7133811227332514782444968660012510417]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [45, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 78], [0, 1]]
 g := ![![[36, 72], [48, 67], [6, 20], [46, 40], [20], [1]], ![[0, 7], [54, 12], [75, 59], [26, 39], [20], [1]]]
 h' := ![![[39, 78], [52, 25], [46, 64], [63, 39], [19, 35], [34, 39], [0, 1]], ![[0, 1], [0, 54], [14, 15], [4, 40], [41, 44], [54, 40], [39, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [20, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [45, 40, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1705, -1575, -325]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![180, 50, -325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![524230478659074212, 454009636330614197, 140299135189263798]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![524230478659074212, 454009636330614197, 140299135189263798]] 
 ![![79, 0, 0], ![44, 1, 0], ![20, 0, 1]] where
  M :=![![![524230478659074212, 454009636330614197, 140299135189263798], ![-16241587451191777765, -457863467665772374, 1048318407850492192], ![-62865992240266708717, -12016912971237918653, -3853831335158177]]]
  hmulB := by decide  
  f := ![![![-12599315601864976890641539667874459574, 1684212820946371766093778070324985225, -540184507655155763157541848219566276]], ![![-6182325534812013615270715030101555053, 826422026245081913412499852708377902, -265061736741636276074706671256082430]], ![![-5295898908198012213912218320105439973, 707928995627565139723344953823512447, -227056979499185190450579818030428303]]]
  g := ![![![-281749066122445904, 454009636330614197, 140299135189263798], ![-215974215581109331, -457863467665772374, 1048318407850492192], ![5898167786340568045, -12016912971237918653, -3853831335158177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![12599315601864976890641539667874459574, -1684212820946371766093778070324985225, 540184507655155763157541848219566276]] ![![524230478659074212, 454009636330614197, 140299135189263798]]
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


lemma PB180I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB180I1 : PrimesBelowBoundCertificateInterval O 31 79 180 where
  m := 11
  g := ![2, 3, 2, 2, 1, 2, 2, 3, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB180I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
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
      exact NI41N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I43N1, I47N1, I59N1, I61N1, I67N0, I67N1, I71N1, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [], [I59N1], [I61N1], [I67N0, I67N1, I67N1], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
