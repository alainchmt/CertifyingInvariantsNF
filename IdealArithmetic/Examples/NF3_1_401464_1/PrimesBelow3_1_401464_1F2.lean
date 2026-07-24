
import IdealArithmetic.Examples.NF3_1_401464_1.RI3_1_401464_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [1, 62, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 9, 37], [74, 73, 46], [0, 1]]
 g := ![![[50, 49, 1], [81, 70, 10], [49, 17], [0, 12], [16, 24, 1], []], ![[45, 40, 40, 11], [48, 63, 62, 21], [76, 3], [47, 75], [37, 24, 54, 48], [73, 41]], ![[66, 18, 32, 82], [48, 74, 2, 35], [52, 9], [16, 64], [1, 11, 75, 74], [64, 41]]]
 h' := ![![[33, 9, 37], [2, 54, 1], [0, 10, 33], [7, 47, 73], [67, 63, 57], [0, 0, 1], [0, 1]], ![[74, 73, 46], [61, 82, 79], [77, 38, 40], [30, 64, 13], [49, 32, 18], [20, 11, 73], [33, 9, 37]], ![[0, 1], [31, 30, 3], [56, 35, 10], [78, 55, 80], [54, 71, 8], [17, 72, 9], [74, 73, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 51], []]
 b := ![[], [43, 54, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [1, 62, 59, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112465, -21746, 1162]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1355, -262, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-303335955384444, 40548417172507, -13005260673778]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-303335955384444, 40548417172507, -13005260673778]] 
 ![![89, 0, 0], ![0, 89, 0], ![19, 54, 1]] where
  M :=![![![-303335955384444, 40548417172507, -13005260673778], ![1588174437352089, -212299130667998, 68091573671236], ![-4005930221080319, 535492502240465, -171750713495491]]]
  hmulB := by decide  
  f := ![![![-11968902, -2670103, -152272]], ![![15450265, -10902998, -5492478]], ![![10497085, -6867528, -3517529]]]
  g := ![![![-631865197558, 8346432511871, -13005260673778], ![3308253231445, -43699372010278, 68091573671236], ![-8344569265910, 110225067764011, -171750713495491]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [27, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 88], [0, 1]]
 g := ![![[66, 9], [80], [81], [21, 42], [11, 4], [1]], ![[48, 80], [80], [81], [26, 47], [3, 85], [1]]]
 h' := ![![[87, 88], [75, 86], [59, 76], [56, 80], [59, 65], [62, 87], [0, 1]], ![[0, 1], [81, 3], [85, 13], [74, 9], [18, 24], [66, 2], [87, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [12, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [27, 2, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![844, -1447, -157]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43, 79, -157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11968902, -2670103, -152272]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-11968902, -2670103, -152272]] 
 ![![89, 0, 0], ![69, 1, 0], ![23, 0, 1]] where
  M :=![![![-11968902, -2670103, -152272], ![15450265, -10902998, -5492478], ![327335393, 28283857, -13573101]]]
  hmulB := by decide  
  f := ![![![-303335955384444, 40548417172507, -13005260673778]], ![![-217325915552523, 29051029822865, -9317656323814]], ![![-123400642639579, 16495574125934, -5290693359465]]]
  g := ![![![1974949, -2670103, -152272], ![10045889, -10902998, -5492478], ![-14742353, 28283857, -13573101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-303335955384444, 40548417172507, -13005260673778]] ![![-11968902, -2670103, -152272]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![749, -100, 32]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![749, -100, 32]] 
 ![![97, 0, 0], ![0, 97, 0], ![81, 9, 1]] where
  M :=![![![749, -100, 32], ![-3908, 525, -168], ![9884, -1316, 425]]]
  hmulB := by decide  
  f := ![![![21, 4, 0]], ![![4, 21, 8]], ![![13, 5, 1]]]
  g := ![![![-19, -4, 32], ![100, 21, -168], ![-253, -53, 425]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [81, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 96], [0, 1]]
 g := ![![[15, 6], [16], [73], [93], [4], [46, 1]], ![[0, 91], [16], [73], [93], [4], [92, 96]]]
 h' := ![![[46, 96], [59, 43], [26, 93], [64, 48], [15, 53], [57, 95], [0, 1]], ![[0, 1], [0, 54], [36, 4], [41, 49], [28, 44], [62, 2], [46, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [1, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [81, 51, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-257728, -273583, -25408]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18560, -463, -25408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -4, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-21, -4, 0]] 
 ![![97, 0, 0], ![78, 1, 0], ![14, 0, 1]] where
  M :=![![![-21, -4, 0], ![-4, -21, -8], ![476, 28, -25]]]
  hmulB := by decide  
  f := ![![![-749, 100, -32]], ![![-562, 75, -24]], ![![-210, 28, -9]]]
  g := ![![![3, -4, 0], ![18, -21, -8], ![-14, 28, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![749, -100, 32]] ![![-21, -4, 0]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16374469099379, -75602049214948, -31212777133464]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![16374469099379, -75602049214948, -31212777133464]] 
 ![![101, 0, 0], ![0, 101, 0], ![17, 2, 1]] where
  M :=![![![16374469099379, -75602049214948, -31212777133464], ![3638718429667268, 234863909033627, -182416875563360], ![10963048815987044, 2495619303912868, 159261859818679]]]
  hmulB := by decide  
  f := ![![![-4877702366063101223922643913, 652026595830960316577095060, -209127172805336135650258408]], ![![25538160159665960458957845612, -3413812156425748274370835057, 1094926018856584497503931712]], ![![-953076959612761396192844433, 127402510219745377851441190, -40862331292795378899408609]]]
  g := ![![![5415759211567, -130460346020, -31212777133464], ![66730745685588, 5937600595647, -182416875563360], ![81738586129401, 21555401824510, 159261859818679]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [59, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 100], [0, 1]]
 g := ![![[51, 47], [25], [87, 78], [85], [80], [21, 1]], ![[28, 54], [25], [8, 23], [85], [80], [42, 100]]]
 h' := ![![[21, 100], [61, 42], [18, 96], [12, 49], [49, 40], [74, 79], [0, 1]], ![[0, 1], [34, 59], [14, 5], [31, 52], [81, 61], [16, 22], [21, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [7, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [59, 80, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-481, -1429, -563]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![90, -3, -563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4877702366063101223922643913, -652026595830960316577095060, 209127172805336135650258408]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![4877702366063101223922643913, -652026595830960316577095060, 209127172805336135650258408]] 
 ![![101, 0, 0], ![96, 1, 0], ![89, 0, 1]] where
  M :=![![![4877702366063101223922643913, -652026595830960316577095060, 209127172805336135650258408], ![-25538160159665960458957845612, 3413812156425748274370835057, -1094926018856584497503931712], ![64416153017148101126708032436, -8610825715919454329926614284, 2761785560594787957793739997]]]
  hmulB := by decide  
  f := ![![![-16374469099379, 75602049214948, 31212777133464]], ![![-51590766962452, 69533988273281, 31473697825504]], ![![-122974025404275, 41910525507104, 25927478267917]]]
  g := ![![![483761754318419559826245261, -652026595830960316577095060, 209127172805336135650258408], ![-2532828826715859153670377116, 3413812156425748274370835057, -1094926018856584497503931712], ![6388678285668114738178417267, -8610825715919454329926614284, 2761785560594787957793739997]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![16374469099379, -75602049214948, -31212777133464]] ![![4877702366063101223922643913, -652026595830960316577095060, 209127172805336135650258408]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [79, 51, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 37, 50], [75, 65, 53], [0, 1]]
 g := ![![[88, 6, 28], [36, 77, 32], [43, 65, 61], [13, 25], [46, 61], [1]], ![[31, 101, 95, 66], [63, 53, 80, 50], [6, 37, 81, 79], [11, 92], [24, 55], [20, 22, 40, 61]], ![[101, 33, 69, 85], [51, 82, 38, 42], [48, 58, 35, 43], [5, 76], [10, 79], [96, 58, 82, 42]]]
 h' := ![![[52, 37, 50], [40, 16, 50], [2, 97, 49], [100, 27, 79], [32, 69, 98], [24, 52, 24], [0, 1]], ![[75, 65, 53], [1, 9, 33], [58, 8, 1], [31, 14, 99], [30, 26, 35], [81, 25, 40], [52, 37, 50]], ![[0, 1], [61, 78, 20], [59, 101, 53], [50, 62, 28], [41, 8, 73], [25, 26, 39], [75, 65, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 15], []]
 b := ![[], [67, 71, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [79, 51, 79, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-126896, -27295, 824]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1232, -265, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀


def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![4, 1, 0]] 
 ![![107, 0, 0], ![4, 1, 0], ![46, 0, 1]] where
  M :=![![![4, 1, 0], ![1, 4, 2], ![-119, -7, 5]]]
  hmulB := by decide  
  f := ![![![-34, 5, -2]], ![![1, 0, 0]], ![![-19, 3, -1]]]
  g := ![![![0, 1, 0], ![-1, 4, 2], ![-3, -7, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2360140672133314025303573662952346499023, -315491674695054868228125694678012218764, 101188942896590954365399265455303968898]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![2360140672133314025303573662952346499023, -315491674695054868228125694678012218764, 101188942896590954365399265455303968898]] 
 ![![107, 0, 0], ![51, 1, 0], ![91, 0, 1]] where
  M :=![![![2360140672133314025303573662952346499023, -315491674695054868228125694678012218764, 101188942896590954365399265455303968898], ![-12356975879389378437710638283859184517626, 1651818071857177344745778804765218716737, -529794406493518782090852123900720468630], ![31168605886226299194126803942999303992342, -4166461679619846047423273860938064509226, 1336326397162122476517653110087206497973]]]
  hmulB := by decide  
  f := ![![![83407878813173093721, 65226180359660512424, 19543511585639327494]], ![![18629440384489797387, 30590079402396111541, 10716962272640804248]], ![![-13112520754169411981, 39698672152487901042, 16731673199687262763]]]
  g := ![![![86374039981227434183987391916806621367, -315491674695054868228125694678012218764, 101188942896590954365399265455303968898], ![-452228098627992652798858075251586695569, 1651818071857177344745778804765218716737, -529794406493518782090852123900720468630], ![1140677097243787871491657362924343949975, -4166461679619846047423273860938064509226, 1336326397162122476517653110087206497973]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![4, 1, 0]] ![![2360140672133314025303573662952346499023, -315491674695054868228125694678012218764, 101188942896590954365399265455303968898]]
  ![![-2916413190856122336496343632049798521534, 389851373076957871833276026053169841681, -125038634907154964629255062079504593038]] where
 M := ![![![-2916413190856122336496343632049798521534, 389851373076957871833276026053169841681, -125038634907154964629255062079504593038]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-2916413190856122336496343632049798521534, 389851373076957871833276026053169841681, -125038634907154964629255062079504593038]] ![![2360140672133314025303573662952346499023, -315491674695054868228125694678012218764, 101188942896590954365399265455303968898]]
  ![![107, 0, 0]] where
 M := ![![![-15597809334117281196396904056939955582335295199848351818855404717691766527945584, 2085036305885437953043595897341632586463210456813203231829933171968082774147461, -668742273143943438953693797922362853370400775858838921094321417042188483128536]]]
 hmul := by decide  
 g := ![![![![-145773919010441880340157981840560332545189674764937867465938361847586603064912, 19486320615751756570500896236837687723955237914142086278784422167926007235023, -6249927786391994756576577550676288349256082017372326365367489878898957786248]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-503688662520355631361984646991, 67330554292690570162390177210, -21595205705837518244977946570]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-503688662520355631361984646991, 67330554292690570162390177210, -21595205705837518244977946570]] 
 ![![109, 0, 0], ![0, 109, 0], ![94, 35, 1]] where
  M :=![![![-503688662520355631361984646991, 67330554292690570162390177210, -21595205705837518244977946570], ![2637160033287355241314765819040, -352522222579493003647139021001, 113065902879543622079802407850], ![-6651838001362414199890820454080, 889184079418929658296879393440, -285191668286802433484748843791]]]
  hmulB := by decide  
  f := ![![![581736560339901, 52461607617410, -23251386322770]], ![![2819376580027040, 744496264599291, 81671828912050]], ![![1363149752337246, 294370334513985, 13484785044019]]]
  g := ![![![14002391503012578749228828721, 7551951871532144116849709240, -21595205705837518244977946570], ![-73312246214584818662262940540, -39539713975812108040735993539, 113065902879543622079802407850], ![184919071721073527960326338186, 99732958435385457158376962625, -285191668286802433484748843791]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [65, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 108], [0, 1]]
 g := ![![[25, 22], [9], [97, 22], [95, 25], [26], [10, 1]], ![[27, 87], [9], [99, 87], [18, 84], [26], [20, 108]]]
 h' := ![![[10, 108], [31, 83], [17, 3], [38, 83], [70, 104], [4, 35], [0, 1]], ![[0, 1], [98, 26], [47, 106], [105, 26], [20, 5], [27, 74], [10, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [34, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [65, 99, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13505, 592, 1082]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1057, -342, 1082]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-581736560339901, -52461607617410, 23251386322770]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-581736560339901, -52461607617410, 23251386322770]] 
 ![![109, 0, 0], ![38, 1, 0], ![96, 0, 1]] where
  M :=![![![-581736560339901, -52461607617410, 23251386322770], ![-2819376580027040, -744496264599291, -81671828912050], ![4778093968137280, -1097606085012640, -796957872216701]]]
  hmulB := by decide  
  f := ![![![503688662520355631361984646991, -67330554292690570162390177210, 21595205705837518244977946570]], ![![151403753600790447251749089602, -20238888445346318004804474431, 6491301962773230011278528090]], ![![504641739479968392758177491424, -67457956802910315540241618400, 21636068037130313623877355179]]]
  g := ![![![-7525950072149, -52461607617410, 23251386322770], ![305614468351402, -744496264599291, -81671828912050], ![1128395237902944, -1097606085012640, -796957872216701]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-503688662520355631361984646991, 67330554292690570162390177210, -21595205705837518244977946570]] ![![-581736560339901, -52461607617410, 23251386322770]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1528613947671561106479095, -204337385481859422940498, 65537970379560892296910]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1528613947671561106479095, -204337385481859422940498, 65537970379560892296910]] 
 ![![113, 0, 0], ![11, 1, 0], ![53, 0, 1]] where
  M :=![![![1528613947671561106479095, -204337385481859422940498, 65537970379560892296910], ![-8003355860649605606272788, 1069848155014634860400725, -343136800584157953584086], ![20187256738428935115213932, -2698530435539320254121844, 865510769532775437460227]]]
  hmulB := by decide  
  f := ![![![1315126089991, 1613097871006, 539938455078]], ![![-426311427375, 135217995447, 85889001796]], ![![-1382947668585, 355631676074, 245711441545]]]
  g := ![![![2679758919073340416711, -204337385481859422940498, 65537970379560892296910], ![-14030399423453252484285, 1069848155014634860400725, -343136800584157953584086], ![35389564107295218806745, -2698530435539320254121844, 865510769532775437460227]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23165296138, 12299040873, 3121910366]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![23165296138, 12299040873, 3121910366]] 
 ![![113, 0, 0], ![105, 1, 0], ![25, 0, 1]] where
  M :=![![![23165296138, 12299040873, 3121910366], ![-359208292681, 1311923576, 27719992112], ![-1660266216945, -282773639169, 13610964449]]]
  hmulB := by decide  
  f := ![![![-7856339592398955184552, 1050195763432445649831, -336833608173411404960]], ![![-6936126212971875146353, 927186290488687768871, -297380273801032899346]], ![![-2656294410119557463993, 355080009351406550526, -113886272354760308177]]]
  g := ![![![-11913997829, 12299040873, 3121910366], ![-10530620097, 1311923576, 27719992112], ![245050369775, -282773639169, 13610964449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-84, -11, 2]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-84, -11, 2]] 
 ![![113, 0, 0], ![109, 1, 0], ![49, 0, 1]] where
  M :=![![![-84, -11, 2], ![-249, -98, -20], ![1183, -49, -109]]]
  hmulB := by decide  
  f := ![![![9702, -1297, 416]], ![![8909, -1191, 382]], ![![5341, -714, 229]]]
  g := ![![![9, -11, 2], ![101, -98, -20], ![105, -49, -109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1528613947671561106479095, -204337385481859422940498, 65537970379560892296910]] ![![23165296138, 12299040873, 3121910366]]
  ![![-9702, 1297, -416]] where
 M := ![![![-9702, 1297, -416]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-9702, 1297, -416]] ![![-84, -11, 2]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2826410146, -377820221, 121179834]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![2826410146, -377820221, 121179834]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 119, 1]] where
  M :=![![![2826410146, -377820221, 121179834], ![-14798220467, 1978151308, -634460608], ![37326276757, -4989587995, 1600331087]]]
  hmulB := by decide  
  f := ![![![38668, 8011, 248]], ![![-21501, 36932, 16270]], ![![-27776, 34041, 15599]]]
  g := ![![![22255198, -116521421, 121179834], ![-116521421, 610070580, -634460608], ![293907691, -1538810924, 1600331087]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [108, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 126], [0, 1]]
 g := ![![[69, 44], [14, 44], [2, 113], [8, 34], [31, 115], [41, 1]], ![[95, 83], [40, 83], [63, 14], [5, 93], [47, 12], [82, 126]]]
 h' := ![![[41, 126], [12, 60], [38, 60], [25, 42], [81, 62], [17, 49], [0, 1]], ![[0, 1], [59, 67], [85, 67], [96, 85], [83, 65], [121, 78], [41, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [119, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [108, 86, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1524, -195, -309]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 288, -309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38668, -8011, -248]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-38668, -8011, -248]] 
 ![![127, 0, 0], ![15, 1, 0], ![15, 0, 1]] where
  M :=![![![-38668, -8011, -248], ![21501, -36932, -16270], ![968933, 71701, -44943]]]
  hmulB := by decide  
  f := ![![![-2826410146, 377820221, -121179834]], ![![-217306549, 29048441, -9316826]], ![![-627735661, 83912530, -26913611]]]
  g := ![![![671, -8011, -248], ![6453, -36932, -16270], ![4469, 71701, -44943]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![2826410146, -377820221, 121179834]] ![![-38668, -8011, -248]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1655152288, 120458041, -77574696]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![1655152288, 120458041, -77574696]] 
 ![![131, 0, 0], ![0, 131, 0], ![110, 115, 1]] where
  M :=![![![1655152288, 120458041, -77574696], ![9351846865, 2198175160, 163341386], ![-9447301031, 4043999561, 2318633201]]]
  hmulB := by decide  
  f := ![![![33864194002384394, -4526794272967387, 1451897352393406]], ![![-177302579207782701, 23700912535630552, -7601691193541368]], ![![-123797834224048800, 16548668689168611, -5307722597185645]]]
  g := ![![![77773808, 69019451, -77574696], ![-65768745, -126611330, 163341386], ![-2019060711, -2004571134, 2318633201]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [16, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 130], [0, 1]]
 g := ![![[23, 41], [104, 43], [65], [123], [91], [101], [1]], ![[0, 90], [0, 88], [65], [123], [91], [101], [1]]]
 h' := ![![[25, 130], [39, 98], [46, 82], [13, 117], [127, 75], [81, 22], [115, 25], [0, 1]], ![[0, 1], [0, 33], [0, 49], [56, 14], [37, 56], [107, 109], [85, 106], [25, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [29, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [16, 106, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1727, -954, 338]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-297, -304, 338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33864194002384394, 4526794272967387, -1451897352393406]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-33864194002384394, 4526794272967387, -1451897352393406]] 
 ![![131, 0, 0], ![31, 1, 0], ![44, 0, 1]] where
  M :=![![![-33864194002384394, 4526794272967387, -1451897352393406], ![177302579207782701, -23700912535630552, 7601691193541368], ![-447218985282334475, 59781973290012869, -19174118262663165]]]
  hmulB := by decide  
  f := ![![![-1655152288, -120458041, 77574696]], ![![-463065403, -45285301, 17110490]], ![![-483812211, -71329415, 8356133]]]
  g := ![![![-842071243962317, 4526794272967387, -1451897352393406], ![4408827903026791, -23700912535630552, 7601691193541368], ![-11120602700118734, 59781973290012869, -19174118262663165]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![1655152288, 120458041, -77574696]] ![![-33864194002384394, 4526794272967387, -1451897352393406]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2348317505, -1056125186, -240888342]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-2348317505, -1056125186, -240888342]] 
 ![![137, 0, 0], ![0, 137, 0], ![117, 106, 1]] where
  M :=![![![-2348317505, -1056125186, -240888342], ![27609587512, -662099111, -2353138714], ![140854862680, 22568841848, -1718224297]]]
  hmulB := by decide  
  f := ![![![395950731840981047, -52928692327618834, 16976037262179466]], ![![-2073077126526975288, 277118471005724785, -88881347393058202]], ![![-1227670917861279293, 164108842504025176, -52635304272343547]]]
  g := ![![![188581157, 178671818, -240888342], ![2211144650, 1815843829, -2353138714], ![2495526317, 1494165090, -1718224297]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [115, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 136], [0, 1]]
 g := ![![[2, 56], [128], [9], [74, 7], [7], [18], [1]], ![[0, 81], [128], [9], [108, 130], [7], [18], [1]]]
 h' := ![![[44, 136], [7, 59], [43, 26], [121, 3], [93, 12], [58, 125], [22, 44], [0, 1]], ![[0, 1], [0, 78], [91, 111], [116, 134], [73, 125], [78, 12], [40, 93], [44, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [3, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [115, 93, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1900, -1575, -590]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![490, 445, -590]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-395950731840981047, 52928692327618834, -16976037262179466]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-395950731840981047, 52928692327618834, -16976037262179466]] 
 ![![137, 0, 0], ![61, 1, 0], ![58, 0, 1]] where
  M :=![![![-395950731840981047, 52928692327618834, -16976037262179466], ![2073077126526975288, -277118471005724785, 88881347393058202], ![-5229024039469334888, 698989501223974520, -224189778678105951]]]
  hmulB := by decide  
  f := ![![![2348317505, 1056125186, 240888342]], ![![844071389, 475078361, 124433048]], ![![-33959470, 282382620, 114523709]]]
  g := ![![![-19270005858535189, 52928692327618834, -16976037262179466], ![100891866489626361, -277118471005724785, 88881347393058202], ![-254484499640887850, 698989501223974520, -224189778678105951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-2348317505, -1056125186, -240888342]] ![![-395950731840981047, 52928692327618834, -16976037262179466]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB180I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB180I2 : PrimesBelowBoundCertificateInterval O 79 137 180 where
  m := 11
  g := ![1, 2, 2, 2, 1, 3, 2, 3, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB180I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N1, I97N1, I101N1, I107N0, I107N1, I109N1, I113N0, I113N1, I113N2, I127N1, I131N1, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [], [I107N0, I107N1, I107N1], [I109N1], [I113N0, I113N1, I113N2], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
