
import IdealArithmetic.Examples.NF3_1_547128_1.RI3_1_547128_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![58, 55, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![58, 55, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![58, 55, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![58, 55, 1], ![254, 284, 546], ![7806, 342, -153]]]
  hmulB := by decide  
  f := ![![![-57, -55, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -55, 139]], ![![0, 0, 1], ![-226, -214, 546], ![120, 63, -153]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [114, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 138], [0, 1]]
 g := ![![[93, 41], [108, 112], [54], [29, 7], [125], [54], [1]], ![[64, 98], [22, 27], [54], [41, 132], [125], [54], [1]]]
 h' := ![![[101, 138], [59, 67], [26, 116], [30, 101], [74, 110], [29, 79], [25, 101], [0, 1]], ![[0, 1], [15, 72], [66, 23], [84, 38], [64, 29], [85, 60], [79, 38], [101, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [16, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [114, 38, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1565, 408, 15]
  a := ![-1, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -3, 15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![10, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![10, 1, 0]] 
 ![![139, 0, 0], ![10, 1, 0], ![14, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![10, 1, 0], ![2, 14, 10], ![144, 6, 6]]]
  hmulB := by decide  
  f := ![![![-279, -1960, -1400], ![0, 19460, 0]], ![![-20, -140, -100], ![1, 1390, 0]], ![![-34, -198, -141], ![82, 1960, 0]]]
  g := ![![![1, 0, 0], ![-10, 139, 0], ![-14, 0, 139]], ![![0, 1, 0], ![-2, 14, 10], ![0, 6, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![58, 55, 1]] ![![139, 0, 0], ![10, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![1390, 139, 0]], ![![8062, 7645, 139], ![834, 834, 556]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![10, 1, 0]]], ![![![58, 55, 1]], ![![6, 6, 4]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3584215536013, -91817230696, -182225297664]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![3584215536013, -91817230696, -182225297664]] 
 ![![149, 0, 0], ![36, 1, 0], ![35, 0, 1]] where
  M :=![![![3584215536013, -91817230696, -182225297664], ![-26424077325008, 2123594827245, -189271116304], ![7552002713472, -2737606956144, 2311456779821]]]
  hmulB := by decide  
  f := ![![![4390447736437290045651369, 711092802867035428233032, 404351049262224596923264]], ![![1461106410813670164140036, 236646081521423186285317, 134564842986990210630032]], ![![1409174595787011068551023, 228235016836880186044520, 129782031493335775821093]]]
  g := ![![![89043766841, -91817230696, -182225297664], ![-645966456612, 2123594827245, -189271116304], ![169160173429, -2737606956144, 2311456779821]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1001024146237, 162129493076, 92192229168]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![1001024146237, 162129493076, 92192229168]] 
 ![![149, 0, 0], ![131, 1, 0], ![124, 0, 1]] where
  M :=![![![1001024146237, 162129493076, 92192229168], ![13599939986344, 2202695493549, 1252526014088], ![12836732877792, 2079083708472, 1182236236445]]]
  hmulB := by decide  
  f := ![![![-20760231, 756476, 817456]], ![![-17452105, 578985, 747528]], ![![-17171316, 725848, 570037]]]
  g := ![![![-212548831299, 162129493076, 92192229168], ![-2887693928963, 2202695493549, 1252526014088], ![-2725641115780, 2079083708472, 1182236236445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![3584215536013, -91817230696, -182225297664]] ![![1001024146237, 162129493076, 92192229168]]
  ![![-20760231, 756476, 817456]] where
 M := ![![![-20760231, 756476, 817456]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-20760231, 756476, 817456]] ![![1001024146237, 162129493076, 92192229168]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31337, -2316, 10]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![31337, -2316, 10]] 
 ![![151, 0, 0], ![0, 151, 0], ![8, 10, 1]] where
  M :=![![![31337, -2316, 10], ![-3192, 22133, -23200], ![-334644, -13776, 40691]]]
  hmulB := by decide  
  f := ![![![-3847753, -623196, -354370]], ![![-52275672, -8466757, -4814480]], ![![-3992588, -646654, -367709]]]
  g := ![![![207, -16, 10], ![1208, 1683, -23200], ![-4372, -2786, 40691]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [21, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 150], [0, 1]]
 g := ![![[25, 36], [150, 11], [146, 10], [10], [48, 29], [50], [1]], ![[0, 115], [113, 140], [30, 141], [10], [74, 122], [50], [1]]]
 h' := ![![[79, 150], [21, 145], [105, 39], [77, 37], [49, 37], [146, 28], [130, 79], [0, 1]], ![[0, 1], [0, 6], [15, 112], [131, 114], [103, 114], [93, 123], [29, 72], [79, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [11, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [21, 72, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7281, 1884, 1789]
  a := ![2, 2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, -106, 1789]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3847753, 623196, 354370]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![3847753, 623196, 354370]] 
 ![![151, 0, 0], ![55, 1, 0], ![23, 0, 1]] where
  M :=![![![3847753, 623196, 354370], ![52275672, 8466757, 4814480], ![49342044, 7991616, 4544299]]]
  hmulB := by decide  
  f := ![![![-31337, 2316, -10]], ![![-11393, 697, 150]], ![![-2557, 444, -271]]]
  g := ![![![-255487, 623196, 354370], ![-3471053, 8466757, 4814480], ![-3276263, 7991616, 4544299]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![31337, -2316, 10]] ![![3847753, 623196, 354370]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [127, 52, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 12], [131, 144], [0, 1]]
 g := ![![[136, 148, 40], [94, 113], [2, 13, 99], [144, 68, 46], [132, 117, 140], [129, 1], []], ![[0, 13, 108], [25, 100], [58, 114, 126], [35, 21, 30], [144, 22, 64], [127, 12], []], ![[92, 153, 9], [139, 101], [20, 30, 89], [113, 68, 81], [42, 18, 110], [103, 144], []]]
 h' := ![![[155, 12], [140, 131, 36], [60, 96, 120], [81, 16, 141], [35, 142, 49], [102, 73, 104], [0, 0, 1], [0, 1]], ![[131, 144], [22, 1, 3], [34, 102, 10], [142, 18, 51], [104, 137, 148], [58, 123, 61], [4, 109, 144], [155, 12]], ![[0, 1], [32, 25, 118], [27, 116, 27], [153, 123, 122], [108, 35, 117], [56, 118, 149], [48, 48, 12], [131, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9], []]
 b := ![[], [100, 156, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [127, 52, 28, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43367912180, -5143994001, -1852170291]
  a := ![-65, -129, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-276228740, -32764293, -11797263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6594464434940235518351100211, 1068063322911533597940448269, 607336375163019389899544304]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![6594464434940235518351100211, 1068063322911533597940448269, 607336375163019389899544304]] 
 ![![163, 0, 0], ![0, 163, 0], ![47, 23, 1]] where
  M :=![![![6594464434940235518351100211, 1068063322911533597940448269, 607336375163019389899544304], ![89592564669297859341415276314, 14510735977564486249510159111, 8251287728463258419806305474], ![84564771730676627654876500080, 13696416439425434266437221262, 7788238519761275635685205871]]]
  hmulB := by decide  
  f := ![![![-12996177291089, -6777910863777, 8194348924974]], ![![1166430423468702, 9058272803647, -100556504337666]], ![![149122113283853, -322434442924, -11287120207385]]]
  g := ![![![-134664694464550158324708479, -79145235005140566685577121, 607336375163019389899544304], ![-1829558028027455744720742828, -1075269213356383174270152557, 8251287728463258419806305474], ![-1726886126982229001363976539, -1014926806841005554320997017, 7788238519761275635685205871]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [119, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 162], [0, 1]]
 g := ![![[110, 100], [41, 150], [65], [60], [16], [22, 55], [1]], ![[0, 63], [39, 13], [65], [60], [16], [43, 108], [1]]]
 h' := ![![[113, 162], [11, 10], [26, 98], [153, 126], [152, 95], [153, 159], [44, 113], [0, 1]], ![[0, 1], [0, 153], [16, 65], [47, 37], [129, 68], [27, 4], [99, 50], [113, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [52, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [119, 50, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4249, 1746, 409]
  a := ![-2, -3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-144, -47, 409]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12996177291089, 6777910863777, -8194348924974]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![12996177291089, 6777910863777, -8194348924974]] 
 ![![163, 0, 0], ![100, 1, 0], ![36, 0, 1]] where
  M :=![![![12996177291089, 6777910863777, -8194348924974], ![-1166430423468702, -9058272803647, 100556504337666], ![1910174941830924, -57664721917026, -87864606488785]]]
  hmulB := by decide  
  f := ![![![-6594464434940235518351100211, -1068063322911533597940448269, -607336375163019389899544304]], ![![-4595331338425284731144326978, -744276492446121754868435497, -423220400274633112943317398]], ![![-1975248413426534394573718452, -319918380762212538603026742, -181916245556012108417600005]]]
  g := ![![![-2268701520169, 6777910863777, -8194348924974], ![-23807590793006, -9058272803647, 100556504337666], ![66501674644968, -57664721917026, -87864606488785]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![6594464434940235518351100211, 1068063322911533597940448269, 607336375163019389899544304]] ![![12996177291089, 6777910863777, -8194348924974]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-68, 33, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-68, 33, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![99, 33, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-68, 33, 1], ![210, 70, 326], ![4638, 210, -191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -33, 167]], ![![-1, 0, 1], ![-192, -64, 326], ![141, 39, -191]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [146, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 166], [0, 1]]
 g := ![![[69, 47], [7, 133], [55, 88], [81], [22], [87, 77], [1]], ![[36, 120], [6, 34], [146, 79], [81], [22], [104, 90], [1]]]
 h' := ![![[113, 166], [147, 106], [153, 119], [78, 64], [61, 9], [157, 32], [21, 113], [0, 1]], ![[0, 1], [101, 61], [73, 48], [129, 103], [76, 158], [99, 135], [98, 54], [113, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112]]
 b := ![[], [9, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [146, 54, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1581, 360, -65]
  a := ![-1, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 15, -65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![8, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![8, 1, 0]] 
 ![![167, 0, 0], ![8, 1, 0], ![24, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![8, 1, 0], ![2, 12, 10], ![144, 6, 4]]]
  hmulB := by decide  
  f := ![![![-1637, -9828, -8190], ![0, 136773, 0]], ![![-78, -468, -390], ![1, 6513, 0]], ![![-240, -1413, -1177], ![99, 19656, 0]]]
  g := ![![![1, 0, 0], ![-8, 167, 0], ![-24, 0, 167]], ![![0, 1, 0], ![-2, 12, 10], ![0, 6, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-68, 33, 1]] ![![167, 0, 0], ![8, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![1336, 167, 0]], ![![-11356, 5511, 167], ![-334, 334, 334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![8, 1, 0]]], ![![![-68, 33, 1]], ![![-2, 2, 2]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91101520099151456830950149325, 14755131859358250305745035480, 8390259365977009791102230348]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![91101520099151456830950149325, 14755131859358250305745035480, 8390259365977009791102230348]] 
 ![![173, 0, 0], ![0, 173, 0], ![110, 102, 1]] where
  M :=![![![91101520099151456830950149325, 14755131859358250305745035480, 8390259365977009791102230348], ![1237707612419405910530211241072, 200463603732446516800543673333, 113990281129674463893041433408], ![1168249420026208927841630849448, 189213903547873619327696977056, 107593326955511543727890080537]]]
  hmulB := by decide  
  f := ![![![451868118273601, -266047049464, -34955364240428]], ![![-5034104544720560, 241071744633177, 137160986467072]], ![![-2657957050885058, 139531746381278, 59443147869953]]]
  g := ![![![-4808248613631905319019047335, -4861568343758940742119551792, 8390259365977009791102230348], ![-65324990241877370622568476496, -66049393476845946822483714071, 113990281129674463893041433408], ![-61659055173873184290325306414, -62342806045747421045763533166, 107593326955511543727890080537]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [145, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 172], [0, 1]]
 g := ![![[153, 149], [139], [94, 25], [72, 149], [31], [59, 124], [1]], ![[99, 24], [139], [107, 148], [18, 24], [31], [165, 49], [1]]]
 h' := ![![[132, 172], [71, 144], [37, 100], [113, 168], [32, 29], [95, 107], [28, 132], [0, 1]], ![[0, 1], [49, 29], [89, 73], [145, 5], [54, 144], [33, 66], [152, 41], [132, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [68, 151]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [145, 41, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51671, 6607, 4768]
  a := ![2, 23, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2733, -2773, 4768]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-451868118273601, 266047049464, 34955364240428]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-451868118273601, 266047049464, 34955364240428]] 
 ![![173, 0, 0], ![22, 1, 0], ![116, 0, 1]] where
  M :=![![![-451868118273601, 266047049464, 34955364240428], ![5034104544720560, -241071744633177, -137160986467072], ![-3946600748285976, 421060653181920, -138334028307605]]]
  hmulB := by decide  
  f := ![![![-91101520099151456830950149325, -14755131859358250305745035480, -8390259365977009791102230348]], ![![-18739543668212358154977540614, -3035124304267792043508291641, -1725872758272651325417864168]], ![![-67838299141779063122727446076, -10987336411753934420775266432, -6247765395426847858356929485]]]
  g := ![![![-26084065926309, 266047049464, 34955364240428], ![151724608999022, -241071744633177, -137160986467072], ![16397758181468, 421060653181920, -138334028307605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![91101520099151456830950149325, 14755131859358250305745035480, 8390259365977009791102230348]] ![![-451868118273601, 266047049464, 34955364240428]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![16, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![16, 1, 0]] 
 ![![179, 0, 0], ![16, 1, 0], ![4, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![16, 1, 0], ![2, 20, 10], ![144, 6, 12]]]
  hmulB := by decide  
  f := ![![![-7967, -80634, -40320], ![-1074, 721728, 0]], ![![-720, -7200, -3600], ![1, 64440, 0]], ![![-180, -1802, -901], ![-2, 16128, 0]]]
  g := ![![![1, 0, 0], ![-16, 179, 0], ![-4, 0, 179]], ![![0, 1, 0], ![-2, 20, 10], ![0, 6, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 5, -6]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![9, 5, -6]] 
 ![![179, 0, 0], ![77, 1, 0], ![3, 0, 1]] where
  M :=![![![9, 5, -6], ![-854, -7, 74], ![1404, -42, -65]]]
  hmulB := by decide  
  f := ![![![-3563, -577, -328]], ![![-1803, -292, -166]], ![![-315, -51, -29]]]
  g := ![![![-2, 5, -6], ![-3, -7, 74], ![27, -42, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![86, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![86, 1, 0]] 
 ![![179, 0, 0], ![86, 1, 0], ![157, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![86, 1, 0], ![2, 90, 10], ![144, 6, 82]]]
  hmulB := by decide  
  f := ![![![-1641, -100973, -11220], ![-1253, 200838, 0]], ![![-820, -48507, -5390], ![-536, 96481, 0]], ![![-1447, -88563, -9841], ![-1083, 176154, 0]]]
  g := ![![![1, 0, 0], ![-86, 179, 0], ![-157, 0, 179]], ![![0, 1, 0], ![-52, 90, 10], ![-74, 6, 82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![16, 1, 0]] ![![9, 5, -6]]
  ![![179, 0, 0], ![16, -44, 1]] where
 M := ![![![1611, 895, -1074]], ![![-710, 73, -22]]]
 hmul := by decide  
 g := ![![![![9, 5, -6], ![0, 0, 0]]], ![![![-18, 39, -1], ![157, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![16, -44, 1]] ![![179, 0, 0], ![86, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![15394, 179, 0]], ![![2864, -7876, 179], ![1432, -3938, -358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![86, 1, 0]]], ![![![16, -44, 1]], ![![8, -22, -2]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-80, -72, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-80, -72, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![101, 109, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-80, -72, 1], ![0, -362, -724], ![-10482, -420, 217]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-101, -109, 181]], ![![-1, -1, 1], ![404, 434, -724], ![-179, -133, 217]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [179, 177, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 180], [0, 1]]
 g := ![![[2, 60], [111], [34, 64], [14], [34, 36], [80, 16], [1]], ![[61, 121], [111], [109, 117], [14], [178, 145], [144, 165], [1]]]
 h' := ![![[4, 180], [140, 153], [68, 103], [127, 173], [68, 106], [160, 175], [2, 4], [0, 1]], ![[0, 1], [28, 28], [118, 78], [95, 8], [130, 75], [136, 6], [18, 177], [4, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [151, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [179, 177, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6811, 911, -890]
  a := ![-2, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![459, 541, -890]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![0, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![0, 1, 0]] 
 ![![181, 0, 0], ![0, 1, 0], ![145, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![0, 1, 0], ![2, 4, 10], ![144, 6, -4]]]
  hmulB := by decide  
  f := ![![![-181, -364, -910], ![0, 16471, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-145, -292, -729], ![72, 13195, 0]]]
  g := ![![![1, 0, 0], ![0, 181, 0], ![-145, 0, 181]], ![![0, 1, 0], ![-8, 4, 10], ![4, 6, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-80, -72, 1]] ![![181, 0, 0], ![0, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![0, 181, 0]], ![![-14480, -13032, 181], ![0, -362, -724]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![0, 1, 0]]], ![![![-80, -72, 1]], ![![0, -2, -4]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-50, -25, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-50, -25, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![141, 166, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-50, -25, 1], ![94, -144, -254], ![-3714, -138, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-141, -166, 191]], ![![-1, -1, 1], ![188, 220, -254], ![-63, -52, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [35, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 190], [0, 1]]
 g := ![![[189, 118], [85, 162], [7, 149], [130, 100], [18, 48], [30, 125], [1]], ![[45, 73], [156, 29], [123, 42], [63, 91], [131, 143], [185, 66], [1]]]
 h' := ![![[70, 190], [81, 140], [137, 60], [34, 63], [134, 10], [96, 96], [156, 70], [0, 1]], ![[0, 1], [140, 51], [135, 131], [51, 128], [70, 181], [131, 95], [90, 121], [70, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [59, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [35, 121, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3331, 2525, 2000]
  a := ![2, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1459, -1725, 2000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![63, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![63, 1, 0]] 
 ![![191, 0, 0], ![63, 1, 0], ![132, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![63, 1, 0], ![2, 67, 10], ![144, 6, 59]]]
  hmulB := by decide  
  f := ![![![-4820, -188927, -28200], ![-2483, 538620, 0]], ![![-1608, -62306, -9300], ![-763, 177630, 0]], ![![-3372, -130568, -19489], ![-1592, 372240, 0]]]
  g := ![![![1, 0, 0], ![-63, 191, 0], ![-132, 0, 191]], ![![0, 1, 0], ![-29, 67, 10], ![-42, 6, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-50, -25, 1]] ![![191, 0, 0], ![63, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![12033, 191, 0]], ![![-9550, -4775, 191], ![-3056, -1719, -191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![63, 1, 0]]], ![![![-50, -25, 1]], ![![-16, -9, -1]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11513673610885, -280908892596, 1195460677060]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-11513673610885, -280908892596, 1195460677060]] 
 ![![193, 0, 0], ![21, 1, 0], ![160, 0, 1]] where
  M :=![![![-11513673610885, -280908892596, 1195460677060], ![171584519711448, -5464545118909, -7590931634200], ![-176733397718664, 12660074769144, 369108053039]]]
  hmulB := by decide  
  f := ![![![-94084754446848179921310349, -15238307289578560559035884, -8665009006810937908910740]], ![![-16860195621470175949993449, -2730738293923201146894673, -1552788735811251554620940]], ![![-84249046292324220654378232, -13645280404931462734232568, -7759160867562603338295761]]]
  g := ![![![-1020146607233, -280908892596, 1195460677060], ![7776627091609, -5464545118909, -7590931634200], ![-2599234488896, 12660074769144, 369108053039]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-225, 26, -10]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-225, 26, -10]] 
 ![![193, 0, 0], ![37, 1, 0], ![138, 0, 1]] where
  M :=![![![-225, 26, -10], ![-1388, -181, 300], ![4884, 36, -419]]]
  hmulB := by decide  
  f := ![![![65039, 10534, 5990]], ![![17047, 2761, 1570]], ![![50826, 8232, 4681]]]
  g := ![![![1, 26, -10], ![-187, -181, 300], ![318, 36, -419]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-138917631037040676131389335971, -22499602216410275431009337602, -12794023125402551448809066850]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-138917631037040676131389335971, -22499602216410275431009337602, -12794023125402551448809066850]] 
 ![![193, 0, 0], ![135, 1, 0], ![73, 0, 1]] where
  M :=![![![-138917631037040676131389335971, -22499602216410275431009337602, -12794023125402551448809066850], ![-1887338534490787959490524301604, -305680178655097086548281087479, -173819929662492548514857108620], ![-1781424082867188796901110993788, -288525890803292269971764827812, -164065430300022537446633587213]]]
  hmulB := by decide  
  f := ![![![8819108052133413, -205474419948974, -470033955358090]], ![![5815977972158279, -116901761932241, -329684934463210]], ![![3460054104890721, -113331018861482, -149750148225047]]]
  g := ![![![19857473348874263019782036893, -22499602216410275431009337602, -12794023125402551448809066850], ![269784147405747537648248660297, -305680178655097086548281087479, -173819929662492548514857108620], ![254644288018025455351768873717, -288525890803292269971764827812, -164065430300022537446633587213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-11513673610885, -280908892596, 1195460677060]] ![![-225, 26, -10]]
  ![![8819108052133413, -205474419948974, -470033955358090]] where
 M := ![![![8819108052133413, -205474419948974, -470033955358090]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![8819108052133413, -205474419948974, -470033955358090]] ![![-138917631037040676131389335971, -22499602216410275431009337602, -12794023125402551448809066850]]
  ![![193, 0, 0]] where
 M := ![![![193, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB210I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB210I3 : PrimesBelowBoundCertificateInterval O 137 193 210 where
  m := 11
  g := ![2, 3, 2, 1, 2, 2, 2, 3, 2, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB210I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![193, 193, 193]
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
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I149N0, I149N1, I151N1, I163N1, I167N1, I173N1, I179N0, I179N1, I179N2, I181N1, I191N1, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [I149N0, I149N1, I149N1], [I151N1], [], [I163N1], [I167N1], [I173N1], [I179N0, I179N1, I179N2], [I181N1], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
