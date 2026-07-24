
import IdealArithmetic.Examples.NF3_1_856596_2.RI3_1_856596_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-11, 5, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-11, 5, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![128, 5, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-11, 5, 1], ![207, 7, 57], ![798, 29, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-128, -5, 139]], ![![-1, 0, 1], ![-51, -2, 57], ![26, 1, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [21, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 138], [0, 1]]
 g := ![![[23, 113], [130, 81], [5], [71, 106], [63], [47], [1]], ![[71, 26], [66, 58], [5], [25, 33], [63], [47], [1]]]
 h' := ![![[73, 138], [50, 104], [88, 9], [38, 127], [28, 84], [10, 87], [118, 73], [0, 1]], ![[0, 1], [136, 35], [50, 130], [135, 12], [44, 55], [106, 52], [26, 66], [73, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [122, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [21, 66, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![972, 468, -240]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![228, 12, -240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-57, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-57, 1, 0]] 
 ![![139, 0, 0], ![82, 1, 0], ![22, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-57, 1, 0], ![6, -54, 12], ![177, 3, -60]]]
  hmulB := by decide  
  f := ![![![24406, -263165, 58500], ![-11815, -677625, 0]], ![![14401, -155200, 34500], ![-6949, -399625, 0]], ![![3862, -41652, 9259], ![-1872, -107250, 0]]]
  g := ![![![1, 0, 0], ![-82, 139, 0], ![-22, 0, 139]], ![![-1, 1, 0], ![30, -54, 12], ![9, 3, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-11, 5, 1]] ![![139, 0, 0], ![-57, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-7923, 139, 0]], ![![-1529, 695, 139], ![834, -278, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-57, 1, 0]]], ![![![-11, 5, 1]], ![![6, -2, 0]]]]
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
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23637312092849716103027869085, 2593838120627294192202054560, 1809101785056290887605900336]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![23637312092849716103027869085, 2593838120627294192202054560, 1809101785056290887605900336]] 
 ![![149, 0, 0], ![14, 1, 0], ![80, 0, 1]] where
  M :=![![![23637312092849716103027869085, 2593838120627294192202054560, 1809101785056290887605900336], ![335774044678727252259456686832, 36846131809900471342451733773, 25698752092358657643606953712], ![301717492051133764798050327888, 33108939352669955003088768384, 23092204871192997076845306749]]]
  hmulB := by decide  
  f := ![![![-1069835108907431, -84041542448416, 177341375278992]], ![![106761628489846, -13198102044923, 6323869924080]], ![![-777791015941184, -30152139391360, 94489698267605]]]
  g := ![![![-1056406472486145460377670615, 2593838120627294192202054560, 1809101785056290887605900336], ![-15006523275493771530358549550, 36846131809900471342451733773, 25698752092358657643606953712], ![-13484456701890505848273939392, 33108939352669955003088768384, 23092204871192997076845306749]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![58, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![58, 1, 0]] 
 ![![149, 0, 0], ![58, 1, 0], ![103, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![58, 1, 0], ![6, 61, 12], ![177, 3, 55]]]
  hmulB := by decide  
  f := ![![![-11893, -142703, -28080], ![-5513, 348660, 0]], ![![-4648, -55496, -10920], ![-2085, 135590, 0]], ![![-8219, -98647, -19411], ![-3817, 241020, 0]]]
  g := ![![![1, 0, 0], ![-58, 149, 0], ![-103, 0, 149]], ![![0, 1, 0], ![-32, 61, 12], ![-38, 3, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-72, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-72, 1, 0]] 
 ![![149, 0, 0], ![77, 1, 0], ![108, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-72, 1, 0], ![6, -69, 12], ![177, 3, -75]]]
  hmulB := by decide  
  f := ![![![16345, -240057, 41760], ![-9387, -518520, 0]], ![![8485, -124030, 21576], ![-4767, -267902, 0]], ![![11844, -174001, 30269], ![-6811, -375840, 0]]]
  g := ![![![1, 0, 0], ![-77, 149, 0], ![-108, 0, 149]], ![![-1, 1, 0], ![27, -69, 12], ![54, 3, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![23637312092849716103027869085, 2593838120627294192202054560, 1809101785056290887605900336]] ![![149, 0, 0], ![58, 1, 0]]
  ![![149, 0, 0], ![-56, -31, 1]] where
 M := ![![![3521959501834607699351152493665, 386481879973466834638106129440, 269556165973387342253279150064], ![1706738146064010786235073093762, 187288742806283534490170898253, 130626655625623529124749173200]]]
 hmul := by decide  
 g := ![![![![20651335287624325779173264981, 940886674877524548639684431, 1862422799435315714817589695], ![-7944831142474699254541714491, 0, 0]], ![![10007616976909068822459895882, 455952766719862469931035891, 902528275591979525728008426], ![-3850057437581420208724082274, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-56, -31, 1]] ![![149, 0, 0], ![-72, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-10728, 149, 0]], ![![-8344, -4619, 149], ![4023, 2086, -447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-72, 1, 0]]], ![![![-56, -31, 1]], ![![27, 14, -3]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-76, 42, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-76, 42, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![75, 42, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-76, 42, 1], ![429, 53, 501], ![7347, 140, -198]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -42, 151]], ![![-1, 0, 1], ![-246, -139, 501], ![147, 56, -198]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [22, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 150], [0, 1]]
 g := ![![[15, 103], [26, 98], [2, 40], [72], [57, 32], [29], [1]], ![[0, 48], [0, 53], [90, 111], [72], [67, 119], [29], [1]]]
 h' := ![![[123, 150], [32, 109], [107, 20], [79, 74], [105, 125], [148, 118], [129, 123], [0, 1]], ![[0, 1], [0, 42], [0, 131], [121, 77], [78, 26], [15, 33], [7, 28], [123, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [131, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [22, 28, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2093, 350, 260]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, -70, 260]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-48, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-48, 1, 0]] 
 ![![151, 0, 0], ![103, 1, 0], ![47, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-48, 1, 0], ![6, -45, 12], ![177, 3, -51]]]
  hmulB := by decide  
  f := ![![![3445, -28702, 7656], ![-1208, -96338, 0]], ![![2371, -19570, 5220], ![-754, -65685, 0]], ![![1085, -8934, 2383], ![-336, -29986, 0]]]
  g := ![![![1, 0, 0], ![-103, 151, 0], ![-47, 0, 151]], ![![-1, 1, 0], ![27, -45, 12], ![15, 3, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-76, 42, 1]] ![![151, 0, 0], ![-48, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-7248, 151, 0]], ![![-11476, 6342, 151], ![4077, -1963, 453]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-48, 1, 0]]], ![![![-76, 42, 1]], ![![27, -13, 3]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [77, 48, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 116, 109], [40, 40, 48], [0, 1]]
 g := ![![[66, 114, 132], [78, 109], [20, 108, 124], [118, 75, 48], [3, 75, 31], [139, 1], []], ![[134, 90, 54, 71], [68, 154], [100, 81, 154, 143], [156, 50, 82, 111], [69, 58, 112, 11], [154, 30], [144, 106]], ![[114, 20, 20, 46], [45, 82], [87, 152, 149, 156], [140, 37, 61, 1], [15, 54, 49, 39], [40, 111], [48, 106]]]
 h' := ![![[99, 116, 109], [75, 93, 140], [30, 73, 100], [20, 3, 76], [83, 148, 131], [130, 2, 119], [0, 0, 1], [0, 1]], ![[40, 40, 48], [75, 149, 37], [75, 151, 25], [2, 81, 70], [155, 10, 20], [93, 130, 111], [126, 44, 40], [99, 116, 109]], ![[0, 1], [20, 72, 137], [119, 90, 32], [42, 73, 11], [54, 156, 6], [102, 25, 84], [102, 113, 116], [40, 40, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 134], []]
 b := ![[], [133, 129, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [77, 48, 18, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21038160454, -1141740424, -464483558]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-134001022, -7272232, -2958494]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![58, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![58, 1, 0]] 
 ![![163, 0, 0], ![58, 1, 0], ![86, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![58, 1, 0], ![6, 61, 12], ![177, 3, 55]]]
  hmulB := by decide  
  f := ![![![5937, 69768, 13728], ![2608, -186472, 0]], ![![2094, 24821, 4884], ![979, -66341, 0]], ![![3126, 36810, 7243], ![1394, -98384, 0]]]
  g := ![![![1, 0, 0], ![-58, 163, 0], ![-86, 0, 163]], ![![0, 1, 0], ![-28, 61, 12], ![-29, 3, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![861689538388804341722, 94557416851754870248, 65950141705624789031]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![861689538388804341722, 94557416851754870248, 65950141705624789031]] 
 ![![163, 0, 0], ![109, 1, 0], ![97, 0, 1]] where
  M :=![![![861689538388804341722, 94557416851754870248, 65950141705624789031], ![12240519583006116879975, 1343212214060943319559, 936838577104184075883], ![10999000454371255388199, 1206974234434011657178, 841817854656038887102]]]
  hmulB := by decide  
  f := ![![![248575789844, 14616073222, -35739928345]], ![![127953927701, 10910160771, -22165886662]], ![![182872824179, 5897228990, -20889602409]]]
  g := ![![![-97191611312258165959, 94557416851754870248, 65950141705624789031], ![-1380631617967745768789, 1343212214060943319559, 936838577104184075883], ![-1240598300617004830019, 1206974234434011657178, 841817854656038887102]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-4, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-4, 1, 0]] 
 ![![163, 0, 0], ![159, 1, 0], ![136, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-4, 1, 0], ![6, -1, 12], ![177, 3, -7]]]
  hmulB := by decide  
  f := ![![![1465, -244, 2928], ![0, -39772, 0]], ![![1429, -238, 2856], ![1, -38794, 0]], ![![1224, -204, 2443], ![68, -33184, 0]]]
  g := ![![![1, 0, 0], ![-159, 163, 0], ![-136, 0, 163]], ![![-1, 1, 0], ![-9, -1, 12], ![4, 3, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![58, 1, 0]] ![![861689538388804341722, 94557416851754870248, 65950141705624789031]]
  ![![163, 0, 0], ![-16, -13, 1]] where
 M := ![![![140455394757375107700686, 15412858946836043850424, 10749873098016840612053]], ![![62218512809556768699851, 6827542391462725793943, 4761946796030421839681]]]
 hmul := by decide  
 g := ![![![![852828443287288915626, 87357777081773586545, 66503960149469503162], ![-90272406346688403353, 0, 0]]], ![![![377783406003622729065, 38697488136825990220, 29459726367888425344], ![-39988601935391491391, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-16, -13, 1]] ![![163, 0, 0], ![-4, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-652, 163, 0]], ![![-2608, -2119, 163], ![163, 0, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-4, 1, 0]]], ![![![-16, -13, 1]], ![![1, 0, -1]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [18, 102, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 139, 63], [7, 27, 104], [0, 1]]
 g := ![![[50, 66, 12], [83, 130, 19], [43, 102, 61], [138, 22], [67, 115], [89, 109, 1], []], ![[164, 127, 120, 58], [118, 53, 98, 114], [29, 136, 152, 115], [139, 130], [162, 154], [0, 65, 50, 2], [70, 128]], ![[114, 108, 142, 104], [15, 109, 107, 135], [106, 67, 64, 119], [135, 75], [2, 50], [91, 5, 118, 40], [29, 128]]]
 h' := ![![[102, 139, 63], [9, 96, 124], [61, 89, 112], [93, 13, 140], [78, 4, 135], [68, 149, 68], [0, 0, 1], [0, 1]], ![[7, 27, 104], [41, 58, 44], [38, 96, 114], [21, 32, 90], [128, 79, 56], [120, 119, 34], [126, 41, 27], [102, 139, 63]], ![[0, 1], [145, 13, 166], [146, 149, 108], [96, 122, 104], [45, 84, 143], [9, 66, 65], [28, 126, 139], [7, 27, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166, 33], []]
 b := ![[], [159, 6, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [18, 102, 58, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-925347, 3507, 24549]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5541, 21, 147]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [132, 69, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 164, 101], [0, 8, 72], [0, 1]]
 g := ![![[138, 50, 106], [80, 1], [170, 122, 95], [56, 14, 24], [142, 157], [110, 122, 1], []], ![[25, 53, 94, 26], [49, 158], [100, 114, 161, 146], [49, 22, 69, 123], [47, 78], [52, 66, 60, 63], [45, 167]], ![[0, 58, 105, 7], [104, 85], [71, 135, 107, 97], [59, 29, 80, 5], [132, 67], [131, 56, 14, 123], [74, 167]]]
 h' := ![![[122, 164, 101], [71, 33, 25], [50, 152, 1], [47, 133, 152], [84, 94, 71], [12, 7, 26], [0, 0, 1], [0, 1]], ![[0, 8, 72], [29, 120, 73], [31, 5, 136], [65, 72, 117], [75, 103, 28], [33, 170, 50], [121, 162, 8], [122, 164, 101]], ![[0, 1], [147, 20, 75], [143, 16, 36], [170, 141, 77], [113, 149, 74], [8, 169, 97], [93, 11, 164], [0, 8, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 48], []]
 b := ![[], [69, 140, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [132, 69, 51, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-563115, -2076, -6228]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3255, -12, -36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![30, -22, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![30, -22, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![30, 157, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![30, -22, 1], ![45, -33, -267], ![-3981, -52, 100]]]
  hmulB := by decide  
  f := ![![![-29, 22, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -157, 179]], ![![0, -1, 1], ![45, 234, -267], ![-39, -88, 100]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [149, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 178], [0, 1]]
 g := ![![[37, 173], [119, 121], [155], [139], [107, 16], [128, 43], [1]], ![[0, 6], [0, 58], [155], [139], [146, 163], [65, 136], [1]]]
 h' := ![![[36, 178], [169, 50], [141, 11], [18, 79], [167, 153], [81, 175], [30, 36], [0, 1]], ![[0, 1], [0, 129], [0, 168], [177, 100], [126, 26], [116, 4], [73, 143], [36, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [132, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [149, 143, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![164968, 39312, 16227]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1798, -14013, 16227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![88, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![88, 1, 0]] 
 ![![179, 0, 0], ![88, 1, 0], ![79, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![88, 1, 0], ![6, 91, 12], ![177, 3, 85]]]
  hmulB := by decide  
  f := ![![![13387, 263036, 34692], ![8055, -517489, 0]], ![![6502, 129288, 17052], ![4118, -254359, 0]], ![![5863, 116088, 15311], ![3647, -228389, 0]]]
  g := ![![![1, 0, 0], ![-88, 179, 0], ![-79, 0, 179]], ![![0, 1, 0], ![-50, 91, 12], ![-38, 3, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![30, -22, 1]] ![![179, 0, 0], ![88, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![15752, 179, 0]], ![![5370, -3938, 179], ![2685, -1969, -179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![88, 1, 0]]], ![![![30, -22, 1]], ![![15, -11, -1]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-37, -46, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-37, -46, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![144, 135, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-37, -46, 1], ![-99, -172, -555], ![-8229, -124, 105]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-144, -135, 181]], ![![-1, -1, 1], ![441, 413, -555], ![-129, -79, 105]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [148, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 180], [0, 1]]
 g := ![![[102, 170], [64], [35, 133], [64], [85, 33], [21, 80], [1]], ![[0, 11], [64], [100, 48], [64], [29, 148], [154, 101], [1]]]
 h' := ![![[108, 180], [176, 52], [69, 8], [76, 26], [90, 8], [150, 24], [33, 108], [0, 1]], ![[0, 1], [0, 129], [28, 173], [169, 155], [49, 173], [27, 157], [113, 73], [108, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [21, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [148, 73, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-359, 82, -49]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37, 37, -49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![12, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![12, 1, 0]] 
 ![![181, 0, 0], ![12, 1, 0], ![76, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![12, 1, 0], ![6, 15, 12], ![177, 3, 9]]]
  hmulB := by decide  
  f := ![![![49537, 124478, 99600], ![3982, -1502300, 0]], ![![3276, 8248, 6600], ![363, -99550, 0]], ![![20800, 52267, 41821], ![1673, -630800, 0]]]
  g := ![![![1, 0, 0], ![-12, 181, 0], ![-76, 0, 181]], ![![0, 1, 0], ![-6, 15, 12], ![-3, 3, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-37, -46, 1]] ![![181, 0, 0], ![12, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![2172, 181, 0]], ![![-6697, -8326, 181], ![-543, -724, -543]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![12, 1, 0]]], ![![![-37, -46, 1]], ![![-3, -4, -3]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![43, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![43, 1, 0]] 
 ![![191, 0, 0], ![43, 1, 0], ![154, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![43, 1, 0], ![6, 46, 12], ![177, 3, 40]]]
  hmulB := by decide  
  f := ![![![28718, 233639, 60960], ![7831, -970280, 0]], ![![6428, 52568, 13716], ![1911, -218313, 0]], ![![23151, 188379, 49151], ![6331, -782320, 0]]]
  g := ![![![1, 0, 0], ![-43, 191, 0], ![-154, 0, 191]], ![![0, 1, 0], ![-20, 46, 12], ![-32, 3, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![67, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![67, 1, 0]] 
 ![![191, 0, 0], ![67, 1, 0], ![119, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![67, 1, 0], ![6, 70, 12], ![177, 3, 64]]]
  hmulB := by decide  
  f := ![![![84756, 1134793, 194568], ![35717, -3096874, 0]], ![![29700, 398024, 68244], ![12607, -1086217, 0]], ![![52764, 707017, 121223], ![22373, -1929466, 0]]]
  g := ![![![1, 0, 0], ![-67, 191, 0], ![-119, 0, 191]], ![![0, 1, 0], ![-32, 70, 12], ![-40, 3, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![81, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![81, 1, 0]] 
 ![![191, 0, 0], ![81, 1, 0], ![102, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![81, 1, 0], ![6, 84, 12], ![177, 3, 78]]]
  hmulB := by decide  
  f := ![![![16345, 278668, 39816], ![8404, -633738, 0]], ![![6903, 118169, 16884], ![3630, -268737, 0]], ![![8691, 148817, 21263], ![4577, -338436, 0]]]
  g := ![![![1, 0, 0], ![-81, 191, 0], ![-102, 0, 191]], ![![0, 1, 0], ![-42, 84, 12], ![-42, 3, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![43, 1, 0]] ![![191, 0, 0], ![67, 1, 0]]
  ![![191, 0, 0], ![-30, 89, 1]] where
 M := ![![![36481, 0, 0], ![12797, 191, 0]], ![![8213, 191, 0], ![2887, 113, 12]]]
 hmul := by decide  
 g := ![![![![191, 0, 0], ![0, 0, 0]], ![![67, 1, 0], ![0, 0, 0]]], ![![![43, 1, 0], ![0, 0, 0]], ![![17, -5, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-30, 89, 1]] ![![191, 0, 0], ![81, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![15471, 191, 0]], ![![-5730, 16999, 191], ![-1719, 7449, 1146]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![81, 1, 0]]], ![![![-30, 89, 1]], ![![-9, 39, 6]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233911658728, 207576582, -18556238387]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![233911658728, 207576582, -18556238387]] 
 ![![193, 0, 0], ![35, 1, 0], ![147, 0, 1]] where
  M :=![![![233911658728, 207576582, -18556238387], ![-3283208735007, 178865673313, 58159634145], ![1651133794683, -259164607672, 159063975434]]]
  hmulB := by decide  
  f := ![![![-43524003831380881553282, -4776102285095039418476, -3331146651313481658521]], ![![-11096423342442421473751, -1217664925486698572181, -849274198254776611888]], ![![-36028958077774811715603, -3953634175557744331558, -2757506949867520692925]]]
  g := ![![![15307842079, 207576582, -18556238387], ![-93745976789, 178865673313, 58159634145], ![-65598493915, -259164607672, 159063975434]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![72, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![72, 1, 0]] 
 ![![193, 0, 0], ![72, 1, 0], ![33, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![72, 1, 0], ![6, 75, 12], ![177, 3, 69]]]
  hmulB := by decide  
  f := ![![![45289, 661394, 105840], ![20458, -1702260, 0]], ![![16860, 246710, 39480], ![7721, -634970, 0]], ![![7737, 113088, 18097], ![3516, -291060, 0]]]
  g := ![![![1, 0, 0], ![-72, 193, 0], ![-33, 0, 193]], ![![0, 1, 0], ![-30, 75, 12], ![-12, 3, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![86, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![86, 1, 0]] 
 ![![193, 0, 0], ![86, 1, 0], ![6, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![86, 1, 0], ![6, 89, 12], ![177, 3, 83]]]
  hmulB := by decide  
  f := ![![![80555, 1482959, 199980], ![43618, -3216345, 0]], ![![35864, 660724, 89100], ![19494, -1433025, 0]], ![![2474, 46102, 6217], ![1424, -99990, 0]]]
  g := ![![![1, 0, 0], ![-86, 193, 0], ![-6, 0, 193]], ![![0, 1, 0], ![-40, 89, 12], ![-3, 3, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![233911658728, 207576582, -18556238387]] ![![193, 0, 0], ![72, 1, 0]]
  ![![193, 0, 0], ![-79, -23, 1]] where
 M := ![![![45144950134504, 40062280326, -3581354008691], ![13558430693409, 193811187217, -1277889529719]]]
 hmul := by decide  
 g := ![![![![200706620784, -9459712946, -18135921451], ![-81121168648, 0, 0]], ![![60237674057, -1911050503, -6494439119], ![-24462779752, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-79, -23, 1]] ![![193, 0, 0], ![86, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![16598, 193, 0]], ![![-15247, -4439, 193], ![-6755, -2123, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![86, 1, 0]]], ![![![-79, -23, 1]], ![![-35, -11, -1]]]]
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


lemma PB262I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB262I3 : PrimesBelowBoundCertificateInterval O 137 193 262 where
  m := 11
  g := ![2, 3, 2, 1, 3, 1, 1, 2, 2, 3, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB262I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![163, 163, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![191, 191, 191]
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
      exact NI149N2
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
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I149N0, I149N1, I149N2, I151N1, I163N0, I163N1, I163N2, I179N1, I181N1, I191N0, I191N1, I191N2, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [I151N1], [], [I163N0, I163N1, I163N2], [], [], [I179N1], [I181N1], [I191N0, I191N1, I191N2], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
