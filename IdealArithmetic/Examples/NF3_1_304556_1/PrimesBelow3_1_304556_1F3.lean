
import IdealArithmetic.Examples.NF3_1_304556_1.RI3_1_304556_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-69, -212, 69]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-69, -212, 69]] 
 ![![139, 0, 0], ![0, 139, 0], ![138, 7, 1]] where
  M :=![![![-69, -212, 69], ![7378, 1035, -567], ![-20422, -494, 823]]]
  hmulB := by decide  
  f := ![![![-4113, -1010, -351]], ![![-39620, -9729, -3381]], ![![-6984, -1715, -596]]]
  g := ![![![-69, -5, 69], ![616, 36, -567], ![-964, -45, 823]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [96, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 138], [0, 1]]
 g := ![![[45, 42], [128, 29], [118], [53, 121], [29], [121], [1]], ![[0, 97], [87, 110], [118], [112, 18], [29], [121], [1]]]
 h' := ![![[128, 138], [83, 96], [37, 53], [55, 102], [114, 128], [102, 86], [43, 128], [0, 1]], ![[0, 1], [0, 43], [10, 86], [45, 37], [96, 11], [129, 53], [25, 11], [128, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [129, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [96, 11, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1125, 465, 126]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-117, -3, 126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4113, -1010, -351]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-4113, -1010, -351]] 
 ![![139, 0, 0], ![117, 1, 0], ![117, 0, 1]] where
  M :=![![![-4113, -1010, -351], ![-39620, -9729, -3381], ![-125842, -30902, -10739]]]
  hmulB := by decide  
  f := ![![![-69, -212, 69]], ![![-5, -171, 54]], ![![-205, -182, 64]]]
  g := ![![![1116, -1010, -351], ![10750, -9729, -3381], ![34145, -30902, -10739]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-69, -212, 69]] ![![-4113, -1010, -351]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![122409211151242099820336422145577962, 30058858966560339201989130651933815, 10446024781129327212957779098731622]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![122409211151242099820336422145577962, 30058858966560339201989130651933815, 10446024781129327212957779098731622]] 
 ![![149, 0, 0], ![29, 1, 0], ![18, 0, 1]] where
  M :=![![![122409211151242099820336422145577962, 30058858966560339201989130651933815, 10446024781129327212957779098731622], ![1179121584890786332627344831512412235, 289545607649311335227660887725283914, 100622601680810344818925171054533067], ![3745207527129069055163031093859447774, 919674784272397170176052812577669164, 319604466615871674429650018377217729]]]
  hmulB := by decide  
  f := ![![![10021102506695065318, 408916600388497873, -456273151826767903]], ![![1616314379822824985, 97847741535122263, -83633857406963379]], ![![1383873817359205972, -35304080292049156, -34115892986755339]]]
  g := ![![![-6290779496237151858191868392870281, 30058858966560339201989130651933815, 10446024781129327212957779098731622], ![-60596697095260594602117275110754473, 289545607649311335227660887725283914, 100622601680810344818925171054533067], ![-192471420240645228319974502024717296, 919674784272397170176052812577669164, 319604466615871674429650018377217729]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3876684458440583468, -951960316533249837, -330824302686296198]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-3876684458440583468, -951960316533249837, -330824302686296198]] 
 ![![149, 0, 0], ![134, 1, 0], ![124, 0, 1]] where
  M :=![![![-3876684458440583468, -951960316533249837, -330824302686296198], ![-37342633612025831617, -9169873301421322636, -3186705252286045709], ![-118610255531481922386, -29125985777356437708, -10121833617954572473]]]
  hmulB := by decide  
  f := ![![![10321796144, 6807702717, -2480661505]], ![![7497017587, 5925257558, -2110511376]], ![![12916525084, 5697252330, -2215859811]]]
  g := ![![![1105424238188695458, -951960316533249837, -330824302686296198], ![10648133154777859527, -9169873301421322636, -3186705252286045709], ![33821336961480857162, -29125985777356437708, -10121833617954572473]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![122409211151242099820336422145577962, 30058858966560339201989130651933815, 10446024781129327212957779098731622]] ![![-3876684458440583468, -951960316533249837, -330824302686296198]]
  ![![-2836024512201754206849314293300606024618501784828651163, -696415408907858108512820912126284532054505597993430910, -242017590471573972371105661453167687028588831741779517]] where
 M := ![![![-2836024512201754206849314293300606024618501784828651163, -696415408907858108512820912126284532054505597993430910, -242017590471573972371105661453167687028588831741779517]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-2836024512201754206849314293300606024618501784828651163, -696415408907858108512820912126284532054505597993430910, -242017590471573972371105661453167687028588831741779517]] ![![-3876684458440583468, -951960316533249837, -330824302686296198]]
  ![![149, 0, 0]] where
 M := ![![![65706125855771306708300735017887489392828744648871465216764900212658422316, 16134824755119357050873931425757653573345367962283560782620184593165516227, 5607158256361533962977560126244610192316074880824866750192274202592079005]]]
 hmul := by decide  
 g := ![![![![440980710441418165827521711529446237535763386905177618904462417534620284, 108287414463888302354858600172870158210371597062305777064564997269567223, 37631934606453248073674900176138323438362918663254139263035397332832745]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [35, 84, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 132, 60], [74, 18, 91], [0, 1]]
 g := ![![[56, 94, 125], [146, 25, 105], [122, 74, 139], [90, 1], [131, 9, 124], [77, 1], []], ![[36, 47, 43, 23], [113, 65, 51, 6], [137, 31, 139, 73], [20, 62], [42, 90, 115, 108], [99, 22], [100, 127]], ![[33, 10, 128, 36], [71, 4, 74, 29], [45, 27, 132, 85], [103, 124], [116, 47, 51, 16], [133, 59], [69, 127]]]
 h' := ![![[3, 132, 60], [24, 101, 124], [109, 69, 16], [26, 146, 21], [96, 82, 1], [23, 141, 107], [0, 0, 1], [0, 1]], ![[74, 18, 91], [58, 70, 138], [28, 27, 49], [86, 58, 78], [22, 130, 106], [30, 59, 118], [133, 27, 18], [3, 132, 60]], ![[0, 1], [49, 131, 40], [133, 55, 86], [64, 98, 52], [14, 90, 44], [46, 102, 77], [41, 124, 132], [74, 18, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 88], []]
 b := ![[], [10, 90, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [35, 84, 74, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1212379, 511588, 143148]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8029, 3388, 948]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀



lemma PB157I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 156 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 156 (by omega)

def PB157I3 : PrimesBelowBoundCertificateInterval O 137 156 157 where
  m := 3
  g := ![2, 3, 1]
  P := ![139, 149, 151]
  hP := PB157I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N1]
    · exact ![I151N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
  β := ![I139N1, I149N0, I149N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
