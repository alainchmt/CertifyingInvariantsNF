
import IdealArithmetic.Examples.NF3_1_628963_1.RI3_1_628963_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47601834541820154449528615065579780899, 5243097642468117026295214718022194263, 2592447239184011542531825278529985699]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![47601834541820154449528615065579780899, 5243097642468117026295214718022194263, 2592447239184011542531825278529985699]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![47601834541820154449528615065579780899, 5243097642468117026295214718022194263, 2592447239184011542531825278529985699], ![386158232310217531954778838179043423421, 42533346391652319246928092830444255231, 21030593733972562046412423033050999917], ![491100270595540519919348818433797438359, 54092173038263678745778945883356362489, 26745850300147874226810884515415449577]]]
  hmulB := by decide  
  f := ![![![-6304514391280963063, 669979426827434030, 84276841717467351]], ![![11554397929117636643, -5470216587930899109, 3181343450702235448]], ![![48821757418168999025, -3019488972695823338, -2357980159692998864]]]
  g := ![![![22504693651318071453498394893524897600, 1325325201642052741881694719746104282, 2592447239184011542531825278529985699], ![182563819288122484954183207572996211752, 10751376328839878600257834898696627657, 21030593733972562046412423033050999917], ![232177210147696322846268966959190994391, 13673161369057902259484030683970456456, 26745850300147874226810884515415449577]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6251, 4305, -807]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2722, 2556, -807]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6304514391280963063, 669979426827434030, 84276841717467351]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-6304514391280963063, 669979426827434030, 84276841717467351]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![-6304514391280963063, 669979426827434030, 84276841717467351], ![11554397929117636643, -5470216587930899109, 3181343450702235448], ![92393631298501324470, -1238740784288181597, -7981580611805700527]]]
  hmulB := by decide  
  f := ![![![47601834541820154449528615065579780899, 5243097642468117026295214718022194263, 2592447239184011542531825278529985699]], ![![216880033426018843202153726622311602160, 23888222017060218136611653774233224747, 11811520486578286794472124155790492808]], ![![269351052568680337184438716749688609629, 29667635340365897886037080300689278376, 14669148769665942884671354896972717638]]]
  g := ![![![-3529385329912932222, 669979426827434030, 84276841717467351], ![6921635533173150152, -5470216587930899109, 3181343450702235448], ![50806976347297603297, -1238740784288181597, -7981580611805700527]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![47601834541820154449528615065579780899, 5243097642468117026295214718022194263, 2592447239184011542531825278529985699]] ![![-6304514391280963063, 669979426827434030, 84276841717467351]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10254132, 52875, 952346]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-10254132, 52875, 952346]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 1]] where
  M :=![![![-10254132, 52875, 952346], ![145603188, -15862458, -1640317], ![-106191645, 31110168, -14169266]]]
  hmulB := by decide  
  f := ![![![-91929974753028, -10125614664626, -5006605555031]], ![![-745759420590491, -82141570752094, -40614862213068]], ![![-316142125694686, -34821431776089, -17217441067884]]]
  g := ![![![-3418044, 17625, 952346], ![48534396, -5287486, -1640317], ![-35397215, 10370056, -14169266]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47571, 870, 1621]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15857, 290, 1621]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-91929974753028, -10125614664626, -5006605555031]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-91929974753028, -10125614664626, -5006605555031]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![-91929974753028, -10125614664626, -5006605555031], ![-745759420590491, -82141570752094, -40614862213068], ![-948426377084058, -104464295328267, -51652323203652]]]
  hmulB := by decide  
  f := ![![![-10254132, 52875, 952346]], ![![41698308, -5252236, 88125]], ![![-38815259, 10387681, -4405640]]]
  g := ![![![-22224046622915, -10125614664626, -5006605555031], ![-180287138957745, -82141570752094, -40614862213068], ![-229281821074624, -104464295328267, -51652323203652]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-10254132, 52875, 952346]] ![![-91929974753028, -10125614664626, -5006605555031]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, 2, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![18, 2, 1]] 
 ![![5, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![18, 2, 1], ![149, 16, 8], ![186, 21, 10]]]
  hmulB := by decide  
  f := ![![![-8, 1, 0]], ![![-2, -1, 1]], ![![29, -1, -2]]]
  g := ![![![3, 2, 1], ![25, 16, 8], ![31, 21, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, -1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![8, -1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![0, 0, 5]] where
  M :=![![![8, -1, 0], ![2, 6, -5], ![-153, 6, 10]]]
  hmulB := by decide  
  f := ![![![-18, -2, -1]], ![![-37, -4, -2]], ![![-186, -21, -10]]]
  g := ![![![2, -1, 0], ![-2, 6, -1], ![-33, 6, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [0, 1]]
 g := ![![[2, 4], [1]], ![[0, 1], [1]]]
 h' := ![![[2, 4], [1, 2], [0, 1]], ![[0, 1], [0, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal' SI5N1 5 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P5P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5212, 2009, -355]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1846, 2009, -71]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N1 B_one_repr
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![18, 2, 1]] ![![8, -1, 0]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [5, 5, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 1], [6, 1, 6], [0, 1]]
 g := ![![[4], [1]], ![[2, 6, 4, 4], [5, 3, 1, 1]], ![[0, 4, 5, 3], [4, 6, 3, 6]]]
 h' := ![![[1, 5, 1], [2, 2], [0, 1]], ![[6, 1, 6], [4, 3, 2], [1, 5, 1]], ![[0, 1], [0, 2, 5], [6, 1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 6], []]
 b := ![[], [3, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [5, 5, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4347546, -296485, 76230]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![621078, -42355, 10890]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11225571881824, -1236439100204, -611356749449]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-11225571881824, -1236439100204, -611356749449]] 
 ![![11, 0, 0], ![0, 11, 0], ![6, 0, 1]] where
  M :=![![![-11225571881824, -1236439100204, -611356749449], ![-91064704465289, -10030309585538, -4959482002122], ![-115812372397332, -12756138130593, -6307266683620]]]
  hmulB := by decide  
  f := ![![![-3124474, 242293, 112334]], ![![16702516, -3313892, 986797]], ![![440355, 337002, -307672]]]
  g := ![![![-687039216830, -112403554564, -611356749449], ![-5573437495687, -911846325958, -4959482002122], ![-7088070208692, -1159648920963, -6307266683620]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [7, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10], [0, 1]]
 g := ![![[4, 3], [0, 3], [1]], ![[8, 8], [4, 8], [1]]]
 h' := ![![[5, 10], [0, 6], [4, 5], [0, 1]], ![[0, 1], [8, 5], [7, 6], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [2, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [7, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18762, 5665, -1240]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2382, 515, -1240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3124474, -242293, -112334]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![3124474, -242293, -112334]] 
 ![![11, 0, 0], ![2, 1, 0], ![9, 0, 1]] where
  M :=![![![3124474, -242293, -112334], ![-16702516, 3313892, -986797], ![-23590749, -2253264, 4058396]]]
  hmulB := by decide  
  f := ![![![11225571881824, 1236439100204, 611356749449]], ![![10319622566267, 1136653435086, 562017772820]], ![![19712956303068, 2171280912039, 1073588857151]]]
  g := ![![![420006, -242293, -112334], ![-1313557, 3313892, -986797], ![-5055435, -2253264, 4058396]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-11225571881824, -1236439100204, -611356749449]] ![![3124474, -242293, -112334]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41540, -3344, -1397]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![41540, -3344, -1397]] 
 ![![13, 0, 0], ![7, 1, 0], ![0, 0, 1]] where
  M :=![![![41540, -3344, -1397], ![-207053, 43234, -13926], ![-343992, -26037, 53816]]]
  hmulB := by decide  
  f := ![![![-1964089682, -216334393, -106966442]], ![![-2283217278, -251484659, -124346475]], ![![-1558706853, -171683556, -84888856]]]
  g := ![![![4996, -3344, -1397], ![-39207, 43234, -13926], ![-12441, -26037, 53816]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1605614541793192, 131888677322195, 51924832435920]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-1605614541793192, 131888677322195, 51924832435920]] 
 ![![13, 0, 0], ![9, 1, 0], ![11, 0, 1]] where
  M :=![![![-1605614541793192, 131888677322195, 51924832435920], ![7680722008051370, -1653386181764322, 555593721739135], ![13947987737985435, 922187406452190, -2077091226181262]]]
  hmulB := by decide  
  f := ![![![-2921872398340277872750707078714, -321829241053128430992564374890, -159128321528668161248742847565]], ![![-3846140484372497897217606972007, -423632624673283203552035239778, -209464958151255329515693985185]], ![![-4791159359956271322482383501248, -527721601208591652013179680315, -260931705148822933808213712453]]]
  g := ![![![-258752753422159, 131888677322195, 51924832435920], ![1265358977292291, -1653386181764322, 555593721739135], ![2192023428300739, 922187406452190, -2077091226181262]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-424903587701671114486441, 12427934368236348434360, 31413220547378895424698]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-424903587701671114486441, 12427934368236348434360, 31413220547378895424698]] 
 ![![13, 0, 0], ![10, 1, 0], ![12, 0, 1]] where
  M :=![![![-424903587701671114486441, 12427934368236348434360, 31413220547378895424698], ![4781366875012498303110074, -588527042249471790165909, -686769253576048677596], ![-1868112507345306140506680, 962068671854085458408874, -575412338627659393053953]]]
  hmulB := by decide  
  f := ![![![-339306440910045998960000434441223091054029675181, -37372862149814221257673665588280647980120995132, -18478994653069668743256190975977832467427621922]], ![![-472738835901576220369450325581559844776652378124, -52069755291492203199426713511132605539301221941, -25745866767202188941109065826863530741540457772]], ![![-582480449344135968519487163937252025962734902056, -64157230496168030467192022748996335331218268786, -31722513371921146645438663928652650371785281561]]]
  g := ![![![-71241659842506257225109, 12427934368236348434360, 31413220547378895424698], ![821144502196163752992332, -588527042249471790165909, -686769253576048677596], ![-352603935565711385226768, 962068671854085458408874, -575412338627659393053953]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![41540, -3344, -1397]] ![![-1605614541793192, 131888677322195, 51924832435920]]
  ![![-111866901330978629655, 9719283240970163638, 3200748576867672374]] where
 M := ![![![-111866901330978629655, 9719283240970163638, 3200748576867672374]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-111866901330978629655, 9719283240970163638, 3200748576867672374]] ![![-424903587701671114486441, 12427934368236348434360, 31413220547378895424698]]
  ![![13, 0, 0]] where
 M := ![![![88024748208526337338169370222955828765838747, -4030995594026468707688471308356538449715866, -5362524772333180658737316264373305416267860]]]
 hmul := by decide  
 g := ![![![![6771134477578949026013028478688909905064519, -310076584155882208283728562181272188439682, -412501905564090819902870481874869647405220]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12016461527434344, 1062178617381550, 329538804621413]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-12016461527434344, 1062178617381550, 329538804621413]] 
 ![![17, 0, 0], ![0, 17, 0], ![6, 11, 1]] where
  M :=![![![-12016461527434344, 1062178617381550, 329538804621413], ![48295079872313089, -11869337120399722, 4651815477664924], ![122968671904807590, 4501708848217329, -15458973980683096]]]
  hmulB := by decide  
  f := ![![![9561567930360989244166890366548, 1053157609502029628124685784981, 520733299922665431590858835258]], ![![77565879669163751777152030224512, 8543483349829055910871108924962, 4224321447664817277441711254389]], ![![59367011894473993313285149384709, 6538971514445151427181208219888, 3233191484442073582526944721493]]]
  g := ![![![-823158491480166, -150749896085529, 329538804621413], ![1199069823901385, -3708194551453758, 4651815477664924], ![12689559752288598, 10267671919748905, -15458973980683096]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [8, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 16], [0, 1]]
 g := ![![[15, 15], [4], [1], [1]], ![[0, 2], [4], [1], [1]]]
 h' := ![![[16, 16], [10, 10], [5, 15], [9, 16], [0, 1]], ![[0, 1], [0, 7], [7, 2], [10, 1], [16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [11, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [8, 1, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40482, 8862, -1052]
  a := ![-6, -2, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2010, 1202, -1052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9561567930360989244166890366548, 1053157609502029628124685784981, 520733299922665431590858835258]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![9561567930360989244166890366548, 1053157609502029628124685784981, 520733299922665431590858835258]] 
 ![![17, 0, 0], ![15, 1, 0], ![3, 0, 1]] where
  M :=![![![9561567930360989244166890366548, 1053157609502029628124685784981, 520733299922665431590858835258], ![77565879669163751777152030224512, 8543483349829055910871108924962, 4224321447664817277441711254389], ![98645118263090681312173864871133, 10865253240435781473750226853628, 5372319511666268261554083455554]]]
  hmulB := by decide  
  f := ![![![-12016461527434344, 1062178617381550, 329538804621413]], ![![-7761873119953063, 239020125901384, 564405738058007]], ![![5112899254264974, 452249688256587, -851197503930521]]]
  g := ![![![-458705653643379498380939583173, 1053157609502029628124685784981, 520733299922665431590858835258], ![-3721137348309796395190572789005, 8543483349829055910871108924962, 4224321447664817277441711254389], ![-4732390522261461504631869899997, 10865253240435781473750226853628, 5372319511666268261554083455554]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-12016461527434344, 1062178617381550, 329538804621413]] ![![9561567930360989244166890366548, 1053157609502029628124685784981, 520733299922665431590858835258]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-116138, -12792, -6325]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-116138, -12792, -6325]] 
 ![![19, 0, 0], ![0, 19, 0], ![14, 7, 1]] where
  M :=![![![-116138, -12792, -6325], ![-942141, -103772, -51310], ![-1198176, -131973, -65254]]]
  hmulB := by decide  
  f := ![![![-182, -3, 20]], ![![3066, -308, -55]], ![![845, -80, -19]]]
  g := ![![![-1452, 1657, -6325], ![-11779, 13442, -51310], ![-14980, 17095, -65254]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [5, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 18], [0, 1]]
 g := ![![[9, 4], [1, 11], [11], [1]], ![[0, 15], [0, 8], [11], [1]]]
 h' := ![![[12, 18], [14, 2], [8, 12], [14, 12], [0, 1]], ![[0, 1], [0, 17], [0, 7], [6, 7], [12, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [5, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [5, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![129875, 50469, -9863]
  a := ![-15, 27, 44]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14103, 6290, -9863]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![182, 3, -20]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![182, 3, -20]] 
 ![![19, 0, 0], ![5, 1, 0], ![4, 0, 1]] where
  M :=![![![182, 3, -20], ![-3066, 308, 55], ![2859, -678, 256]]]
  hmulB := by decide  
  f := ![![![116138, 12792, 6325]], ![![80149, 8828, 4365]], ![![87512, 9639, 4766]]]
  g := ![![![13, 3, -20], ![-254, 308, 55], ![275, -678, 256]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-116138, -12792, -6325]] ![![182, 3, -20]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [18, 6, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 4, 22], [4, 18, 1], [0, 1]]
 g := ![![[13, 11, 12], [18, 15, 2], [17, 0, 1], []], ![[1, 15, 11, 10], [4, 6, 21, 5], [11, 1, 11, 21], [15, 1]], ![[0, 14, 11, 9], [12, 6, 10, 8], [7, 11, 5, 16], [13, 1]]]
 h' := ![![[19, 4, 22], [21, 16, 14], [16, 13, 5], [0, 0, 1], [0, 1]], ![[4, 18, 1], [12, 13, 6], [5, 19, 8], [22, 21, 18], [19, 4, 22]], ![[0, 1], [0, 17, 3], [13, 14, 10], [12, 2, 4], [4, 18, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 7], []]
 b := ![[], [13, 15, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [18, 6, 0, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26335, -8648, -4370]
  a := ![1, -4, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1145, -376, -190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61608, -643, -5466]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![61608, -643, -5466]] 
 ![![29, 0, 0], ![0, 29, 0], ![24, 19, 1]] where
  M :=![![![61608, -643, -5466], ![-835012, 93118, 7717], ![557541, -176520, 84758]]]
  hmulB := by decide  
  f := ![![![319127596, 35150266, 17380033]], ![![2588844517, 285147930, 140991264]], ![![2073775685, 228415743, 112940060]]]
  g := ![![![6648, 3559, -5466], ![-35180, -1845, 7717], ![-50919, -61618, 84758]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [18, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 28], [0, 1]]
 g := ![![[13, 9], [28], [21, 22], [27, 1]], ![[24, 20], [28], [6, 7], [25, 28]]]
 h' := ![![[27, 28], [19, 26], [28, 17], [7, 15], [0, 1]], ![[0, 1], [25, 3], [23, 12], [6, 14], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [6, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [18, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6423, 5306, -1099]
  a := ![5, -7, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1131, 903, -1099]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-319127596, -35150266, -17380033]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-319127596, -35150266, -17380033]] 
 ![![29, 0, 0], ![23, 1, 0], ![18, 0, 1]] where
  M :=![![![-319127596, -35150266, -17380033], ![-2588844517, -285147930, -140991264], ![-3292386738, -362639493, -179306932]]]
  hmulB := by decide  
  f := ![![![-61608, 643, 5466]], ![![-20068, -2701, 4069]], ![![-57465, 6486, 470]]]
  g := ![![![27661004, -35150266, -17380033], ![224393125, -285147930, -140991264], ![285374013, -362639493, -179306932]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![61608, -643, -5466]] ![![-319127596, -35150266, -17380033]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10117843756758351879216, -1114428535339639016702, -551028681271921828965]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-10117843756758351879216, -1114428535339639016702, -551028681271921828965]] 
 ![![31, 0, 0], ![0, 31, 0], ![4, 20, 1]] where
  M :=![![![-10117843756758351879216, -1114428535339639016702, -551028681271921828965], ![-82078531163924761798241, -9040528739806098938830, -4470085314154351425580], ![-104384124154334150079606, -11497375269935586255633, -5684871960991386529952]]]
  hmulB := by decide  
  f := ![![![-21140501420, 8508304789, -4641058910]], ![![-727098622808, 23722461618, 51823641765]], ![![-411865701933, 9815408992, 32203733042]]]
  g := ![![![-255281581666795631076, 319553067422541856858, -551028681271921828965], ![-2070909351848624390191, 2592296049783255792670, -4470085314154351425580], ![-2633697945495761418058, 3296776256448133688497, -5684871960991386529952]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [28, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 30], [0, 1]]
 g := ![![[21, 10], [15, 16], [9, 16], [1, 1]], ![[0, 21], [0, 15], [25, 15], [2, 30]]]
 h' := ![![[1, 30], [14, 17], [27, 4], [3, 4], [0, 1]], ![[0, 1], [0, 14], [0, 27], [7, 27], [1, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [12, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [28, 30, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3459, 307, 113]
  a := ![-1, 5, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![97, -63, 113]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21140501420, -8508304789, 4641058910]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![21140501420, -8508304789, 4641058910]] 
 ![![31, 0, 0], ![26, 1, 0], ![9, 0, 1]] where
  M :=![![![21140501420, -8508304789, 4641058910], ![727098622808, -23722461618, -51823641765], ![-1858697701917, 204204772764, 19592875358]]]
  hmulB := by decide  
  f := ![![![10117843756758351879216, 1114428535339639016702, 551028681271921828965]], ![![11133628027085222924447, 1226311956730216560422, 606349387974978031570]], ![![6304668321456752161050, 694426841548139916321, 343359035239957515827]]]
  g := ![![![6470545024, -8508304789, 4641058910], ![58396625831, -23722461618, -51823641765], ![-236914763613, 204204772764, 19592875358]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-10117843756758351879216, -1114428535339639016702, -551028681271921828965]] ![![21140501420, -8508304789, 4641058910]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB225I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB225I0 : PrimesBelowBoundCertificateInterval O 1 31 225 where
  m := 11
  g := ![2, 2, 2, 1, 2, 3, 2, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB225I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![9, 3]
    · exact ![5, 25]
    · exact ![343]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I11N0, I11N1, I13N0, I13N1, I13N2, I17N1, I19N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1], [], [I11N0, I11N1], [I13N0, I13N1, I13N2], [I17N1], [I19N1], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
