
import IdealArithmetic.Examples.NF3_3_701244_1.RI3_3_701244_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 73, 12]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![181, 73, 12]] 
 ![![139, 0, 0], ![0, 139, 0], ![73, 64, 1]] where
  M :=![![![181, 73, 12], ![2040, 865, 146], ![12410, 5181, 865]]]
  hmulB := by decide  
  f := ![![![59, 7, -2]], ![![-340, -55, 14]], ![![-117, -20, 5]]]
  g := ![![![-5, -5, 12], ![-62, -61, 146], ![-365, -361, 865]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [23, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 138], [0, 1]]
 g := ![![[30, 79], [117, 83], [46], [12, 121], [44], [25], [1]], ![[8, 60], [115, 56], [46], [61, 18], [44], [25], [1]]]
 h' := ![![[5, 138], [89, 94], [58, 19], [2, 121], [131, 11], [93, 34], [116, 5], [0, 1]], ![[0, 1], [3, 45], [14, 120], [51, 18], [47, 128], [124, 105], [2, 134], [5, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [2, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [23, 134, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![363, 65, -75]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42, 35, -75]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 7, -2]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![59, 7, -2]] 
 ![![139, 0, 0], ![11, 1, 0], ![9, 0, 1]] where
  M :=![![![59, 7, -2], ![-340, -55, 14], ![1190, 229, -55]]]
  hmulB := by decide  
  f := ![![![181, 73, 12]], ![![29, 12, 2]], ![![101, 42, 7]]]
  g := ![![![0, 7, -2], ![1, -55, 14], ![-6, 229, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![181, 73, 12]] ![![59, 7, -2]]
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
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-540943, -17278, 10488]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-540943, -17278, 10488]] 
 ![![149, 0, 0], ![0, 149, 0], ![27, 108, 1]] where
  M :=![![![-540943, -17278, 10488], ![1782960, 56873, -34556], ![-2937260, -93366, 56873]]]
  hmulB := by decide  
  f := ![![![54917, 23014, 3856]], ![![655520, 274709, 46028]], ![![511351, 214292, 35905]]]
  g := ![![![-5531, -7718, 10488], ![18228, 25429, -34556], ![-30019, -41850, 56873]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [124, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 148], [0, 1]]
 g := ![![[140, 143], [20], [57, 102], [110], [42, 22], [114], [1]], ![[0, 6], [20], [53, 47], [110], [9, 127], [114], [1]]]
 h' := ![![[73, 148], [106, 21], [84, 136], [117, 20], [7, 109], [48, 52], [25, 73], [0, 1]], ![[0, 1], [0, 128], [29, 13], [87, 129], [67, 40], [119, 97], [139, 76], [73, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [8, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [124, 76, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1991, -67, 743]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-148, -539, 743]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54917, 23014, 3856]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![54917, 23014, 3856]] 
 ![![149, 0, 0], ![82, 1, 0], ![65, 0, 1]] where
  M :=![![![54917, 23014, 3856], ![655520, 274709, 46028], ![3912380, 1639558, 274709]]]
  hmulB := by decide  
  f := ![![![-540943, -17278, 10488]], ![![-285734, -9127, 5540]], ![![-255695, -8164, 4957]]]
  g := ![![![-13979, 23014, 3856], ![-166862, 274709, 46028], ![-995889, 1639558, 274709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-540943, -17278, 10488]] ![![54917, 23014, 3856]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![427457, 179767, 30398]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![427457, 179767, 30398]] 
 ![![151, 0, 0], ![76, 1, 0], ![132, 0, 1]] where
  M :=![![![427457, 179767, 30398], ![5167660, 2160143, 359534], ![30560390, 12830549, 2160143]]]
  hmulB := by decide  
  f := ![![![53199176283, 1700601821, -1031678336]], ![![25614252188, 818802977, -496730794]], ![![48419825026, 1547821759, -938993571]]]
  g := ![![![-114221, 179767, 30398], ![-1367296, 2160143, 359534], ![-8143710, 12830549, 2160143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129, -25, 6]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-129, -25, 6]] 
 ![![151, 0, 0], ![150, 1, 0], ![75, 0, 1]] where
  M :=![![![-129, -25, 6], ![1020, 213, -50], ![-4250, -915, 213]]]
  hmulB := by decide  
  f := ![![![381, 165, 28]], ![![410, 177, 30]], ![![375, 160, 27]]]
  g := ![![![21, -25, 6], ![-180, 213, -50], ![775, -915, 213]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![427457, 179767, 30398]] ![![427457, 179767, 30398]]
  ![![2040668957289, 855188117702, 143290213378]] where
 M := ![![![2040668957289, 855188117702, 143290213378]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI151N1 : IdealMulLeCertificate' Table 
  ![![2040668957289, 855188117702, 143290213378]] ![![-129, -25, 6]]
  ![![151, 0, 0]] where
 M := ![![![62177709259, 27799897431, 5423308148]]]
 hmul := by decide  
 g := ![![![![411772909, 184105281, 35915948]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1019, -34, 20]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-1019, -34, 20]] 
 ![![157, 0, 0], ![52, 1, 0], ![61, 0, 1]] where
  M :=![![![-1019, -34, 20], ![3400, 121, -68], ![-5780, -238, 121]]]
  hmulB := by decide  
  f := ![![![-1543, -646, -108]], ![![-628, -263, -44]], ![![-1299, -544, -91]]]
  g := ![![![-3, -34, 20], ![8, 121, -68], ![-5, -238, 121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-723, -23, 14]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-723, -23, 14]] 
 ![![157, 0, 0], ![110, 1, 0], ![73, 0, 1]] where
  M :=![![![-723, -23, 14], ![2380, 75, -46], ![-3910, -121, 75]]]
  hmulB := by decide  
  f := ![![![-59, -31, -8]], ![![-50, -25, -6]], ![![-61, -30, -7]]]
  g := ![![![5, -23, 14], ![-16, 75, -46], ![25, -121, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9801, -4107, -688]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-9801, -4107, -688]] 
 ![![157, 0, 0], ![152, 1, 0], ![66, 0, 1]] where
  M :=![![![-9801, -4107, -688], ![-116960, -49017, -8214], ![-698190, -292579, -49017]]]
  hmulB := by decide  
  f := ![![![-577617, -18467, 11202]], ![![-547092, -17491, 10610]], ![![-262816, -8403, 5097]]]
  g := ![![![4203, -4107, -688], ![50164, -49017, -8214], ![299420, -292579, -49017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-1019, -34, 20]] ![![-723, -23, 14]]
  ![![577617, 18467, -11202]] where
 M := ![![![577617, 18467, -11202]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![577617, 18467, -11202]] ![![-9801, -4107, -688]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20227, -4441, 1028]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-20227, -4441, 1028]] 
 ![![163, 0, 0], ![0, 163, 0], ![16, 97, 1]] where
  M :=![![![-20227, -4441, 1028], ![174760, 38369, -8882], ![-754970, -165757, 38369]]]
  hmulB := by decide  
  f := ![![![451, 9, -10]], ![![-1700, -119, 18]], ![![-958, -72, 9]]]
  g := ![![![-225, -639, 1028], ![1944, 5521, -8882], ![-8398, -23850, 38369]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [34, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 162], [0, 1]]
 g := ![![[73, 24], [58, 119], [53], [61], [91], [111, 65], [1]], ![[0, 139], [56, 44], [53], [61], [91], [151, 98], [1]]]
 h' := ![![[126, 162], [147, 26], [137, 49], [132, 78], [139, 77], [138, 55], [129, 126], [0, 1]], ![[0, 1], [0, 137], [117, 114], [17, 85], [61, 86], [59, 108], [31, 37], [126, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [12, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [34, 37, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1422, -120, 150]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -90, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-451, -9, 10]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-451, -9, 10]] 
 ![![163, 0, 0], ![132, 1, 0], ![90, 0, 1]] where
  M :=![![![-451, -9, 10], ![1700, 119, -18], ![-1530, 337, 119]]]
  hmulB := by decide  
  f := ![![![20227, 4441, -1028]], ![![15308, 3361, -778]], ![![15800, 3469, -803]]]
  g := ![![![-1, -9, 10], ![-76, 119, -18], ![-348, 337, 119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-20227, -4441, 1028]] ![![-451, -9, 10]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1753, -56, 34]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-1753, -56, 34]] 
 ![![167, 0, 0], ![103, 1, 0], ![123, 0, 1]] where
  M :=![![![-1753, -56, 34], ![5780, 185, -112], ![-9520, -302, 185]]]
  hmulB := by decide  
  f := ![![![401, 92, -18]], ![![229, 53, -10]], ![![389, 90, -17]]]
  g := ![![![-1, -56, 34], ![3, 185, -112], ![-7, -302, 185]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72321, -15861, 3686]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-72321, -15861, 3686]] 
 ![![167, 0, 0], ![113, 1, 0], ![45, 0, 1]] where
  M :=![![![-72321, -15861, 3686], ![626620, 137781, -31722], ![-2696370, -590767, 137781]]]
  hmulB := by decide  
  f := ![![![-243293187, -7777279, 4718124]], ![![-159820653, -5108938, 3099362]], ![![-73475035, -2348754, 1424883]]]
  g := ![![![9306, -15861, 3686], ![-80929, 137781, -31722], ![346468, -590767, 137781]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175839, -5621, 3410]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-175839, -5621, 3410]] 
 ![![167, 0, 0], ![118, 1, 0], ![52, 0, 1]] where
  M :=![![![-175839, -5621, 3410], ![579700, 18531, -11242], ![-955570, -30547, 18531]]]
  hmulB := by decide  
  f := ![![![-11413, -2519, 572]], ![![-7482, -1653, 374]], ![![-6118, -1353, 305]]]
  g := ![![![1857, -5621, 3410], ![-6122, 18531, -11242], ![10092, -30547, 18531]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-1753, -56, 34]] ![![-72321, -15861, 3686]]
  ![![11413, 2519, -572]] where
 M := ![![![11413, 2519, -572]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![11413, 2519, -572]] ![![-175839, -5621, 3410]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![991168133, 31684369, -19221476]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![991168133, 31684369, -19221476]] 
 ![![173, 0, 0], ![0, 173, 0], ![72, 18, 1]] where
  M :=![![![991168133, 31684369, -19221476], ![-3267650920, -104455999, 63368738], ![5386342730, 172183573, -104455999]]]
  hmulB := by decide  
  f := ![![![-10099, -3271, -126]], ![![-21420, -17281, -6542]], ![![-9646, -4299, -833]]]
  g := ![![![13728985, 2183069, -19221476], ![-45261272, -7197071, 63368738], ![74607946, 11863535, -104455999]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [91, 162, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 172], [0, 1]]
 g := ![![[36, 149], [124], [38, 55], [96, 15], [47], [21, 121], [1]], ![[118, 24], [124], [124, 118], [88, 158], [47], [141, 52], [1]]]
 h' := ![![[11, 172], [138, 144], [2, 41], [87, 125], [112, 19], [165, 96], [82, 11], [0, 1]], ![[0, 1], [165, 29], [107, 132], [78, 48], [148, 154], [10, 77], [30, 162], [11, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [116, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [91, 162, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-766, 587, 23]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14, 1, 23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10099, 3271, 126]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![10099, 3271, 126]] 
 ![![173, 0, 0], ![137, 1, 0], ![44, 0, 1]] where
  M :=![![![10099, 3271, 126], ![21420, 17281, 6542], ![556070, 197157, 17281]]]
  hmulB := by decide  
  f := ![![![-991168133, -31684369, 19221476]], ![![-766025337, -24487298, 14855338]], ![![-283223934, -9053733, 5492491]]]
  g := ![![![-2564, 3271, 126], ![-15225, 17281, 6542], ![-157311, 197157, 17281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![991168133, 31684369, -19221476]] ![![10099, 3271, 126]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [88, 119, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 5, 12], [109, 173, 167], [0, 1]]
 g := ![![[90, 126, 31], [171, 117, 81], [138, 135], [22, 138], [121, 89, 52], [168, 65, 1], []], ![[159, 47, 138, 142], [99, 120, 42, 64], [118, 48], [13, 101], [136, 106, 48, 147], [82, 79, 171, 74], [172, 144]], ![[178, 97, 56, 127], [167, 162, 66, 140], [77, 171], [2, 39], [13, 99, 125, 6], [96, 38, 88, 58], [17, 144]]]
 h' := ![![[135, 5, 12], [167, 12, 63], [103, 72, 9], [84, 73, 99], [92, 103, 73], [73, 64, 54], [0, 0, 1], [0, 1]], ![[109, 173, 167], [31, 121, 124], [34, 113, 94], [173, 154, 103], [171, 43, 82], [99, 91, 86], [46, 72, 173], [135, 5, 12]], ![[0, 1], [53, 46, 171], [102, 173, 76], [104, 131, 156], [82, 33, 24], [51, 24, 39], [3, 107, 5], [109, 173, 167]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 161], []]
 b := ![[], [63, 66, 91], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [88, 119, 114, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5012, 2506, 2506]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, 14, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -19, -4]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-43, -19, -4]] 
 ![![181, 0, 0], ![0, 181, 0], ![56, 50, 1]] where
  M :=![![![-43, -19, -4], ![-680, -271, -38], ![-3230, -1423, -271]]]
  hmulB := by decide  
  f := ![![![-107, -3, 2]], ![![340, 7, -6]], ![![58, 1, -1]]]
  g := ![![![1, 1, -4], ![8, 9, -38], ![66, 67, -271]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [68, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 180], [0, 1]]
 g := ![![[153, 43], [27], [118, 42], [178], [179, 126], [42, 148], [1]], ![[32, 138], [27], [84, 139], [178], [77, 55], [17, 33], [1]]]
 h' := ![![[94, 180], [135, 119], [121, 82], [57, 122], [136, 84], [40, 137], [113, 94], [0, 1]], ![[0, 1], [99, 62], [46, 99], [122, 59], [68, 97], [67, 44], [80, 87], [94, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [8, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [68, 87, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6616, 3942, 868]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-232, -218, 868]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 3, -2]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![107, 3, -2]] 
 ![![181, 0, 0], ![81, 1, 0], ![68, 0, 1]] where
  M :=![![![107, 3, -2], ![-340, -7, 6], ![510, 1, -7]]]
  hmulB := by decide  
  f := ![![![43, 19, 4]], ![![23, 10, 2]], ![![34, 15, 3]]]
  g := ![![![0, 3, -2], ![-1, -7, 6], ![5, 1, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-43, -19, -4]] ![![107, 3, -2]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB187I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 186 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 186 (by omega)

def PB187I3 : PrimesBelowBoundCertificateInterval O 137 186 187 where
  m := 9
  g := ![2, 2, 3, 3, 2, 3, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB187I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
  β := ![I139N1, I149N1, I151N0, I151N1, I157N0, I157N1, I157N2, I163N1, I167N0, I167N1, I167N2, I173N1, I181N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N0, I151N1], [I157N0, I157N1, I157N2], [I163N1], [I167N0, I167N1, I167N2], [I173N1], [], [I181N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
