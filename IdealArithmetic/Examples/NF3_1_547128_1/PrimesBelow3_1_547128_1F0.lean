
import IdealArithmetic.Examples.NF3_1_547128_1.RI3_1_547128_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113740441, 31995009, -42766889]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![113740441, 31995009, -42766889]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![113740441, 31995009, -42766889], ![-6094441998, -14880857, 491017646], ![9482706642, -321232614, -399141596]]]
  hmulB := by decide  
  f := ![![![-163670450957534416, -26508658502412210, -15073706043384941]], ![![-1111815493626127962, -180073660613746451, -102395880425291168]], ![![-1131257393179504691, -183222541018752381, -104186438690867493]]]
  g := ![![![78253665, 31995009, -42766889], ![-3292729822, -14880857, 491017646], ![4940924119, -321232614, -399141596]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-4, 1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-4, 1, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-4, 1, 1], ![146, 6, 6], ![30, 18, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![9, 11, 2], ![-3, 0, -1]], ![![-3, -12, -3], ![6, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-2, 1, 1], ![73, 6, 6], ![15, 18, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![113740441, 31995009, -42766889]] ![![2, 0, 0], ![-4, 1, 1]]
  ![![2, 0, 0], ![0, 1, 0]] where
 M := ![![![227480882, 63990018, -85533778], ![2933302880, -464093507, 262943606]]]
 hmul := by decide  
 g := ![![![![113740441, 25596007, -42766889], ![12798004, 0, 0]], ![![1466651440, -185637403, 131471803], ![-92818701, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![-4, 1, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![-8, 2, 2]], ![![0, 2, 0], ![146, 6, 6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![-4, 1, 1]]], ![![![0, 1, 0]], ![![73, 3, 3]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3627897497, -815397344, 1146784628]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-3627897497, -815397344, 1146784628]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-3627897497, -815397344, 1146784628], ![163506191744, -8779105, -12741111952], ![-248150665128, 8869031472, 9954753531]]]
  hmulB := by decide  
  f := ![![![112913929064065583589, 18287948546689834080, 10399136587929053428]], ![![548988498273076315127, 88916163775029691519, 50560691901037060172]], ![![482654339899808005576, 78172443445095881872, 44451454722889242707]]]
  g := ![![![-937500051, -815397344, 1146784628], ![54504990283, -8779105, -12741111952], ![-85673232200, 8869031472, 9954753531]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-3627897497, -815397344, 1146784628]] ![![-3627897497, -815397344, 1146784628]]
  ![![-404736242423639515311, 13136205399595557504, 17644610088627700840]] where
 M := ![![![-404736242423639515311, 13136205399595557504, 17644610088627700840]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-404736242423639515311, 13136205399595557504, 17644610088627700840]] ![![-3627897497, -815397344, 1146784628]]
  ![![3, 0, 0]] where
 M := ![![![-762329209728436615684732183977, 486396135153478955282136416544, -455867420243740325770941461076]]]
 hmul := by decide  
 g := ![![![![-254109736576145538561577394659, 162132045051159651760712138848, -151955806747913441923647153692]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![2, 6, 10], ![144, 6, -2]]]
  hmulB := by decide  
  f := ![![![1493, -46, -24], ![590, 0, -60]], ![![496, -16, -8], ![201, 0, -20]], ![![1194, -37, -19], ![473, 0, -48]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![-4, 0, 5]], ![![0, 1, 0], ![-10, 6, 10], ![28, 6, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-1, 1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![2, 3, 10], ![144, 6, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![0, 0, 1]], ![![-1, 1, 0], ![-2, 3, 2], ![24, 6, -1]]]
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
  c := ![-7436, 1746, 1030]
  a := ![2, 2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2884, 1746, 206]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N1 B_one_repr
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![10, 5, 0], ![0, 5, 10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-1, 1, 0]]], ![![![2, 1, 0]], ![![0, 1, 2]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-347079455981, 1844480033, 25111537446]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-347079455981, 1844480033, 25111537446]] 
 ![![7, 0, 0], ![0, 7, 0], ![4, 2, 1]] where
  M :=![![![-347079455981, 1844480033, 25111537446], ![3619750352290, -189032311173, -82001349454], ![-2597110144092, 312405329550, -128453539099]]]
  hmulB := by decide  
  f := ![![![-7128503996279553231261, -1154558302765869377081, -656520301253965033168]], ![![-96848039986102703530354, -15685859014866820938593, -8919501822642833638138]], ![![-44803311030379542357752, -7256506381777130863716, -4126291192400469775771]]]
  g := ![![![-63932229395, -6911227837, 25111537446], ![563965107158, -3575658895, -82001349454], ![-297613712528, 81330343964, -128453539099]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[3, 2], [3, 1]], ![[2, 5], [6, 6]]]
 h' := ![![[3, 6], [3, 3], [0, 1]], ![[0, 1], [5, 4], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1968131, 1304298, 543033]
  a := ![-65, -129, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29143, 31176, 543033]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7128503996279553231261, 1154558302765869377081, 656520301253965033168]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7128503996279553231261, 1154558302765869377081, 656520301253965033168]] 
 ![![7, 0, 0], ![5, 1, 0], ![2, 0, 1]] where
  M :=![![![7128503996279553231261, 1154558302765869377081, 656520301253965033168], ![96848039986102703530354, 15685859014866820938593, 8919501822642833638138], ![91413081255333176518512, 14805593431642796660502, 8418953496501761021449]]]
  hmulB := by decide  
  f := ![![![347079455981, -1844480033, -25111537446]], ![![-269193296055, 25687130144, -6222333968]], ![![470181293722, -45156327088, 11175780601]]]
  g := ![![![6095982848896611360, 1154558302765869377081, 656520301253965033168], ![82820180926133080159, 15685859014866820938593, 8919501822642833638138], ![78172443445095881872, 14805593431642796660502, 8418953496501761021449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-347079455981, 1844480033, 25111537446]] ![![7128503996279553231261, 1154558302765869377081, 656520301253965033168]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [3, 3, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 2, 1], [2, 8, 10], [0, 1]]
 g := ![![[10, 4, 5], [0, 5, 1], []], ![[8, 9, 7, 3], [0, 7, 6, 9], [9, 1]], ![[6, 8, 0, 10], [8, 0, 6, 7], [0, 1]]]
 h' := ![![[3, 2, 1], [0, 7, 4], [0, 0, 1], [0, 1]], ![[2, 8, 10], [4, 8, 6], [4, 4, 8], [3, 2, 1]], ![[0, 1], [8, 7, 1], [4, 7, 2], [2, 8, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 1], []]
 b := ![[], [1, 3, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [3, 3, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2243417, -271359, -6138]
  a := ![-2, -3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-203947, -24669, -558]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![2, 1, 0]] 
 ![![13, 0, 0], ![2, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![2, 1, 0], ![2, 6, 10], ![144, 6, -2]]]
  hmulB := by decide  
  f := ![![![-65, -208, -350], ![-26, 455, 0]], ![![-10, -30, -50], ![1, 65, 0]], ![![-60, -192, -323], ![-24, 420, 0]]]
  g := ![![![1, 0, 0], ![-2, 13, 0], ![-12, 0, 13]], ![![0, 1, 0], ![-10, 6, 10], ![12, 6, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-349897, -14744, 42906]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-349897, -14744, 42906]] 
 ![![13, 0, 0], ![5, 1, 0], ![10, 0, 1]] where
  M :=![![![-349897, -14744, 42906], ![6148976, -151437, -319064], ![-7014420, 426408, 95233]]]
  hmulB := by decide  
  f := ![![![121629642291, 19699577000, 11201835538]], ![![173893206379, 28164372963, 16015200426]], ![![213540481506, 34585789112, 19666631501]]]
  g := ![![![-54249, -14744, 42906], ![776677, -151437, -319064], ![-776830, 426408, 95233]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![6, 1, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0], ![6, 1, 0]] 
 ![![13, 0, 0], ![6, 1, 0], ![2, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![6, 1, 0], ![2, 10, 10], ![144, 6, 2]]]
  hmulB := by decide  
  f := ![![![-179, -1306, -1320], ![-182, 1716, 0]], ![![-84, -594, -600], ![-77, 780, 0]], ![![-28, -201, -203], ![-27, 264, 0]]]
  g := ![![![1, 0, 0], ![-6, 13, 0], ![-2, 0, 13]], ![![0, 1, 0], ![-6, 10, 10], ![8, 6, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![2, 1, 0]] ![![-349897, -14744, 42906]]
  ![![13, 0, 0], ![-4, 5, 1]] where
 M := ![![![-4548661, -191672, 557778]], ![![5449182, -180925, -233252]]]
 hmul := by decide  
 g := ![![![![-323945, -47184, 36418], ![84344, 0, 0]]], ![![![385726, 27885, -9582], ![-108686, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-4, 5, 1]] ![![13, 0, 0], ![6, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![78, 13, 0]], ![![-52, 65, 13], ![130, 52, 52]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![6, 1, 0]]], ![![![-4, 5, 1]], ![![10, 4, 4]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![3, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![3, 1, 0]] 
 ![![17, 0, 0], ![3, 1, 0], ![10, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![3, 1, 0], ![2, 7, 10], ![144, 6, -1]]]
  hmulB := by decide  
  f := ![![![-80, -293, -420], ![-17, 714, 0]], ![![-14, -49, -70], ![1, 119, 0]], ![![-46, -172, -247], ![-16, 420, 0]]]
  g := ![![![1, 0, 0], ![-3, 17, 0], ![-10, 0, 17]], ![![0, 1, 0], ![-7, 7, 10], ![8, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62477, -10119, -5754]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-62477, -10119, -5754]] 
 ![![17, 0, 0], ![11, 1, 0], ![16, 0, 1]] where
  M :=![![![-62477, -10119, -5754], ![-848814, -137477, -78174], ![-801180, -129762, -73787]]]
  hmulB := by decide  
  f := ![![![-811, 105, -48]], ![![-919, 28, 42]], ![![448, 102, -143]]]
  g := ![![![8288, -10119, -5754], ![112601, -137477, -78174], ![106282, -129762, -73787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![3, 1, 0]] ![![17, 0, 0], ![3, 1, 0]]
  ![![-811, 105, -48]] where
 M := ![![![289, 0, 0], ![51, 17, 0]], ![![51, 17, 0], ![11, 10, 10]]]
 hmul := by decide  
 g := ![![![![-1062109, -172023, -97818]], ![![-1036245, -167834, -95436]]], ![![![-1036245, -167834, -95436]], ![![-1011011, -163747, -93112]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-811, 105, -48]] ![![-62477, -10119, -5754]]
  ![![17, 0, 0]] where
 M := ![![![17, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-11, -7, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-11, -7, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![8, 12, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-11, -7, 1], ![130, -33, -74], ![-1122, -30, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -12, 19]], ![![-1, -1, 1], ![38, 45, -74], ![-70, -18, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [2, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18], [0, 1]]
 g := ![![[4, 6], [14, 6], [7], [1]], ![[13, 13], [4, 13], [7], [1]]]
 h' := ![![[11, 18], [10, 14], [9, 14], [17, 11], [0, 1]], ![[0, 1], [12, 5], [11, 5], [5, 8], [11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [8, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [2, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51462, 5848, 4471]
  a := ![2, 23, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![826, -2516, 4471]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-2, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-2, 1, 0]] 
 ![![19, 0, 0], ![17, 1, 0], ![12, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-2, 1, 0], ![2, 2, 10], ![144, 6, -6]]]
  hmulB := by decide  
  f := ![![![-105, -109, -540], ![19, 1026, 0]], ![![-93, -97, -480], ![20, 912, 0]], ![![-66, -69, -341], ![15, 648, 0]]]
  g := ![![![1, 0, 0], ![-17, 19, 0], ![-12, 0, 19]], ![![-1, 1, 0], ![-8, 2, 10], ![6, 6, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-11, -7, 1]] ![![19, 0, 0], ![-2, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-38, 19, 0]], ![![-209, -133, 19], ![152, -19, -76]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-2, 1, 0]]], ![![![-11, -7, 1]], ![![8, -1, -4]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73536499, -811838, 6594572]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-73536499, -811838, 6594572]] 
 ![![23, 0, 0], ![0, 23, 0], ![19, 9, 1]] where
  M :=![![![-73536499, -811838, 6594572], ![947994692, -37216419, -34496668], ![-868685880, 74263836, -10937999]]]
  hmulB := by decide  
  f := ![![![129083828204523, 20906883924610, 11888350462324]], ![![1753736234423876, 284041466676907, 161515437396804]], ![![864849486006075, 140074152337187, 79650827914017]]]
  g := ![![![-8644929, -2615782, 6594572], ![69714408, 11880591, -34496668], ![-28733213, 7508949, -10937999]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [18, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 22], [0, 1]]
 g := ![![[21, 9], [17, 4], [4, 8], [1]], ![[0, 14], [0, 19], [16, 15], [1]]]
 h' := ![![[13, 22], [16, 20], [20, 2], [5, 13], [0, 1]], ![[0, 1], [0, 3], [0, 21], [13, 10], [13, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [21, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [18, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6638, 1078, 613]
  a := ![-2, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-795, -193, 613]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![129083828204523, 20906883924610, 11888350462324]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![129083828204523, 20906883924610, 11888350462324]] 
 ![![23, 0, 0], ![6, 1, 0], ![8, 0, 1]] where
  M :=![![![129083828204523, 20906883924610, 11888350462324], ![1753736234423876, 284041466676907, 161515437396804], ![1655319332438904, 268101509095548, 152451446666999]]]
  hmulB := by decide  
  f := ![![![-73536499, -811838, 6594572]], ![![22033726, -1829889, 220468]], ![![-63346864, 2946484, 1818199]]]
  g := ![![![-3976707784423, 20906883924610, 11888350462324], ![-54027654991826, 284041466676907, 161515437396804], ![-50995708498712, 268101509095548, 152451446666999]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-73536499, -811838, 6594572]] ![![129083828204523, 20906883924610, 11888350462324]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![944958017, 2211051, -76031492]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![944958017, 2211051, -76031492]] 
 ![![29, 0, 0], ![0, 29, 0], ![15, 10, 1]] where
  M :=![![![944958017, 2211051, -76031492], ![-10944112746, 497613269, 326236478], ![8985981432, -899111598, 251830385]]]
  hmulB := by decide  
  f := ![![![-14435763523236221, -2338068498133089, -1329503612827094]], ![![-196124657243367714, -31765059192731141, -18062670530022514]], ![![-81479361281072295, -13196692198001083, -7504078673751009]]]
  g := ![![![71911393, 26293999, -76031492], ![-546126204, -95336259, 326236478], ![179604333, -117841912, 251830385]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [14, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28], [0, 1]]
 g := ![![[16, 13], [20], [13, 6], [8, 1]], ![[4, 16], [20], [3, 23], [16, 28]]]
 h' := ![![[8, 28], [16, 19], [21, 7], [4, 21], [0, 1]], ![[0, 1], [23, 10], [19, 22], [27, 8], [8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [14, 21, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3110, 2025, 1000]
  a := ![2, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-410, -275, 1000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14435763523236221, 2338068498133089, 1329503612827094]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![14435763523236221, 2338068498133089, 1329503612827094]] 
 ![![29, 0, 0], ![20, 1, 0], ![16, 0, 1]] where
  M :=![![![14435763523236221, 2338068498133089, 1329503612827094], ![196124657243367714, 31765059192731141, 18062670530022514], ![185118451868876100, 29982454342723662, 17049022046147711]]]
  hmulB := by decide  
  f := ![![![-944958017, -2211051, 76031492]], ![![-274311986, -18683941, 41185978]], ![![-831217576, 29783958, 33264603]]]
  g := ![![![-1848195318781347, 2338068498133089, 1329503612827094], ![-25109629485917770, 31765059192731141, 18062670530022514], ![-23700516818067604, 29982454342723662, 17049022046147711]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![944958017, 2211051, -76031492]] ![![14435763523236221, 2338068498133089, 1329503612827094]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3545, -43, 322]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-3545, -43, 322]] 
 ![![31, 0, 0], ![0, 31, 0], ![12, 30, 1]] where
  M :=![![![-3545, -43, 322], ![46282, -1785, -1718], ![-42900, 3606, -475]]]
  hmulB := by decide  
  f := ![![![-227193, -36797, -20924]], ![![-3086650, -499925, -284274]], ![![-3169008, -513264, -291859]]]
  g := ![![![-239, -313, 322], ![2158, 1605, -1718], ![-1200, 576, -475]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [12, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 30], [0, 1]]
 g := ![![[1, 4], [12, 10], [17, 2], [19, 1]], ![[15, 27], [16, 21], [24, 29], [7, 30]]]
 h' := ![![[19, 30], [11, 29], [13, 17], [20, 8], [0, 1]], ![[0, 1], [4, 2], [26, 14], [17, 23], [19, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [27, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [12, 12, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12177, 7580, 2960]
  a := ![-5, -10, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-753, -2620, 2960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227193, 36797, 20924]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![227193, 36797, 20924]] 
 ![![31, 0, 0], ![14, 1, 0], ![6, 0, 1]] where
  M :=![![![227193, 36797, 20924], ![3086650, 499925, 284274], ![2913432, 471870, 268321]]]
  hmulB := by decide  
  f := ![![![3545, 43, -322]], ![![108, 77, -90]], ![![2070, -108, -47]]]
  g := ![![![-13339, 36797, 20924], ![-181224, 499925, 284274], ![-171054, 471870, 268321]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-3545, -43, 322]] ![![227193, 36797, 20924]]
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


lemma PB210I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB210I0 : PrimesBelowBoundCertificateInterval O 1 31 210 where
  m := 11
  g := ![3, 3, 2, 2, 1, 3, 3, 2, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB210I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![5, 25]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![361, 19]
    · exact ![529, 23]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I13N0, I13N1, I13N2, I17N0, I17N1, I19N1, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1], [I7N0, I7N1], [], [I13N0, I13N1, I13N2], [I17N0, I17N0, I17N1], [I19N1], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
