
import IdealArithmetic.Examples.NF3_3_670761_1.RI3_3_670761_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [70, 35, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 48, 89], [130, 90, 50], [0, 1]]
 g := ![![[101, 57, 79], [95, 78, 65], [21, 47], [135, 104, 49], [21, 55], [10, 1], []], ![[87, 80, 37, 96], [32, 15, 119, 77], [71, 41], [33, 81, 90, 106], [14, 112], [66, 38], [45, 137]], ![[54, 45, 75, 40], [4, 8, 29, 32], [61, 1], [83, 31, 134, 135], [74, 99], [13, 80], [84, 137]]]
 h' := ![![[19, 48, 89], [22, 49, 45], [63, 87, 75], [2, 55, 73], [84, 32, 7], [134, 136, 65], [0, 0, 1], [0, 1]], ![[130, 90, 50], [131, 119, 71], [68, 130, 37], [112, 40, 67], [73, 89, 3], [48, 121, 23], [130, 111, 90], [19, 48, 89]], ![[0, 1], [85, 110, 23], [120, 61, 27], [130, 44, 138], [69, 18, 129], [55, 21, 51], [39, 28, 48], [130, 90, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 19], []]
 b := ![[], [16, 63, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [70, 35, 129, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![142197, 9869, -443410]
  a := ![5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1023, 71, -3190]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![2, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![2, 1, 0]] 
 ![![149, 0, 0], ![2, 1, 0], ![122, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![2, 1, 0], ![-5, -3, 11], ![6, 23, 7]]]
  hmulB := by decide  
  f := ![![![749, 449, -1650], ![149, 22350, 0]], ![![10, 6, -22], ![1, 298, 0]], ![![614, 368, -1351], ![68, 18300, 0]]]
  g := ![![![1, 0, 0], ![-2, 149, 0], ![-122, 0, 149]], ![![0, 1, 0], ![-9, -3, 11], ![-6, 23, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![10, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![10, 1, 0]] 
 ![![149, 0, 0], ![10, 1, 0], ![144, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![10, 1, 0], ![-5, 5, 11], ![6, 23, 15]]]
  hmulB := by decide  
  f := ![![![-7104, 7127, 15675], ![-298, -212325, 0]], ![![-475, 475, 1045], ![1, -14155, 0]], ![![-6864, 6888, 15149], ![-312, -205200, 0]]]
  g := ![![![1, 0, 0], ![-10, 149, 0], ![-144, 0, 149]], ![![0, 1, 0], ![-11, 5, 11], ![-16, 23, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-12, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-12, 1, 0]] 
 ![![149, 0, 0], ![137, 1, 0], ![130, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-12, 1, 0], ![-5, -17, 11], ![6, 23, -7]]]
  hmulB := by decide  
  f := ![![![9265, 31623, -20460], ![-447, 277140, 0]], ![![8515, 29073, -18810], ![-446, 254790, 0]], ![![8078, 27591, -17851], ![-459, 241800, 0]]]
  g := ![![![1, 0, 0], ![-137, 149, 0], ![-130, 0, 149]], ![![-1, 1, 0], ![6, -17, 11], ![-15, 23, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![2, 1, 0]] ![![149, 0, 0], ![10, 1, 0]]
  ![![149, 0, 0], ![42, -40, 1]] where
 M := ![![![22201, 0, 0], ![1490, 149, 0]], ![![298, 149, 0], ![15, 7, 11]]]
 hmul := by decide  
 g := ![![![![107, 40, -1], ![149, 0, 0]], ![![-32, 41, -1], ![149, 0, 0]]], ![![![-40, 41, -1], ![149, 0, 0]], ![![-3, 3, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![42, -40, 1]] ![![149, 0, 0], ![-12, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-1788, 149, 0]], ![![6258, -5960, 149], ![-298, 745, -447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-12, 1, 0]]], ![![![42, -40, 1]], ![![-2, 5, -3]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [138, 70, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 124, 70], [95, 26, 81], [0, 1]]
 g := ![![[3, 129, 125], [81, 38, 95], [94, 11, 34], [2, 47], [1, 138, 94], [134, 1], []], ![[54, 146, 70, 15], [14, 127, 4, 28], [63, 11, 79, 54], [63, 148], [23, 117, 79, 107], [14, 72], [47, 68]], ![[110, 114, 70, 100], [57, 15, 86, 47], [18, 95, 113, 5], [79, 121], [84, 79, 39, 148], [55, 125], [36, 68]]]
 h' := ![![[39, 124, 70], [147, 3, 124], [14, 29, 104], [44, 102, 51], [13, 131, 97], [81, 146, 68], [0, 0, 1], [0, 1]], ![[95, 26, 81], [80, 37, 112], [148, 32, 53], [108, 127, 10], [73, 21, 65], [53, 0, 59], [18, 18, 26], [39, 124, 70]], ![[0, 1], [66, 111, 66], [85, 90, 145], [107, 73, 90], [99, 150, 140], [58, 5, 24], [131, 133, 124], [95, 26, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146, 118], []]
 b := ![[], [130, 10, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [138, 70, 17, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4676017, -5749476, 8812360]
  a := ![-11, -13, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30967, -38076, 58360]
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

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![27, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![27, 1, 0]] 
 ![![157, 0, 0], ![27, 1, 0], ![74, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![27, 1, 0], ![-5, 22, 11], ![6, 23, 32]]]
  hmulB := by decide  
  f := ![![![8745, -39432, -19712], ![1256, 281344, 0]], ![![1486, -6778, -3388], ![315, 48356, 0]], ![![4116, -18586, -9291], ![626, 132608, 0]]]
  g := ![![![1, 0, 0], ![-27, 157, 0], ![-74, 0, 157]], ![![0, 1, 0], ![-9, 22, 11], ![-19, 23, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![64, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![64, 1, 0]] 
 ![![157, 0, 0], ![64, 1, 0], ![113, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![64, 1, 0], ![-5, 59, 11], ![6, 23, 69]]]
  hmulB := by decide  
  f := ![![![16661, -223055, -41580], ![5495, 593460, 0]], ![![6804, -90874, -16940], ![2199, 241780, 0]], ![![11977, -160543, -29927], ![3991, 427140, 0]]]
  g := ![![![1, 0, 0], ![-64, 157, 0], ![-113, 0, 157]], ![![0, 1, 0], ![-32, 59, 11], ![-59, 23, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![66, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![66, 1, 0]] 
 ![![157, 0, 0], ![66, 1, 0], ![76, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![66, 1, 0], ![-5, 61, 11], ![6, 23, 71]]]
  hmulB := by decide  
  f := ![![![8752, -122080, -22011], ![2983, 314157, 0]], ![![3677, -51309, -9251], ![1257, 132037, 0]], ![![4240, -59096, -10655], ![1436, 152076, 0]]]
  g := ![![![1, 0, 0], ![-66, 157, 0], ![-76, 0, 157]], ![![0, 1, 0], ![-31, 61, 11], ![-44, 23, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![27, 1, 0]] ![![157, 0, 0], ![64, 1, 0]]
  ![![157, 0, 0], ![-86, -35, 1]] where
 M := ![![![24649, 0, 0], ![10048, 157, 0]], ![![4239, 157, 0], ![1723, 86, 11]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![64, 1, 0], ![0, 0, 0]]], ![![![27, 1, 0], ![0, 0, 0]], ![![17, 3, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-86, -35, 1]] ![![157, 0, 0], ![66, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![10362, 157, 0]], ![![-13502, -5495, 157], ![-5495, -2198, -314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![66, 1, 0]]], ![![![-86, -35, 1]], ![![-35, -14, -2]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [58, 116, 140, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 82, 139], [61, 80, 24], [0, 1]]
 g := ![![[40], [157, 139, 60], [14, 93], [97, 140], [45, 113], [87, 23, 1], []], ![[21, 44, 162, 99], [22, 27, 2, 72], [70, 95], [27, 65], [137, 61], [155, 154, 48, 109], [21, 87]], ![[51, 59, 156, 64], [144, 10, 10, 43], [155, 53], [119, 83], [31, 6], [26, 63, 34, 6], [136, 87]]]
 h' := ![![[125, 82, 139], [22, 23], [39, 111, 95], [6, 10, 16], [47, 64, 38], [7, 147, 90], [0, 0, 1], [0, 1]], ![[61, 80, 24], [126, 93, 100], [13, 3, 46], [145, 142, 62], [9, 11, 37], [91, 131, 86], [63, 141, 80], [125, 82, 139]], ![[0, 1], [121, 47, 63], [26, 49, 22], [122, 11, 85], [129, 88, 88], [42, 48, 150], [71, 22, 82], [61, 80, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 91], []]
 b := ![[], [66, 17, 160], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [58, 116, 140, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53899851568, 45605547016, -123585239765]
  a := ![261, 262, -587]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![330673936, 279788632, -758191655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![38, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![38, 1, 0]] 
 ![![167, 0, 0], ![38, 1, 0], ![7, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![38, 1, 0], ![-5, 33, 11], ![6, 23, 43]]]
  hmulB := by decide  
  f := ![![![-16915, 116178, 38720], ![-3006, -587840, 0]], ![![-3848, 26404, 8800], ![-667, -133600, 0]], ![![-737, 4869, 1623], ![-3, -24640, 0]]]
  g := ![![![1, 0, 0], ![-38, 167, 0], ![-7, 0, 167]], ![![0, 1, 0], ![-8, 33, 11], ![-7, 23, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-24, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-24, 1, 0]] 
 ![![167, 0, 0], ![143, 1, 0], ![164, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-24, 1, 0], ![-5, -29, 11], ![6, 23, -19]]]
  hmulB := by decide  
  f := ![![![84305, 496534, -188320], ![-9018, 2859040, 0]], ![![72192, 425157, -161249], ![-7681, 2448053, 0]], ![![82796, 487614, -184937], ![-8818, 2807680, 0]]]
  g := ![![![1, 0, 0], ![-143, 167, 0], ![-164, 0, 167]], ![![-1, 1, 0], ![14, -29, 11], ![-1, 23, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-14, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-14, 1, 0]] 
 ![![167, 0, 0], ![153, 1, 0], ![112, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-14, 1, 0], ![-5, -19, 11], ![6, 23, -9]]]
  hmulB := by decide  
  f := ![![![57071, 217950, -126170], ![-3340, 1915490, 0]], ![![52275, 199671, -115588], ![-3172, 1754836, 0]], ![![38276, 146170, -84617], ![-2230, 1284640, 0]]]
  g := ![![![1, 0, 0], ![-153, 167, 0], ![-112, 0, 167]], ![![-1, 1, 0], ![10, -19, 11], ![-15, 23, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![38, 1, 0]] ![![167, 0, 0], ![-24, 1, 0]]
  ![![167, 0, 0], ![-53, 16, 1]] where
 M := ![![![27889, 0, 0], ![-4008, 167, 0]], ![![6346, 167, 0], ![-917, 9, 11]]]
 hmul := by decide  
 g := ![![![![167, 0, 0], ![0, 0, 0]], ![![29, -15, -1], ![167, 0, 0]]], ![![![38, 1, 0], ![0, 0, 0]], ![![-2, -1, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-53, 16, 1]] ![![167, 0, 0], ![-14, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-2338, 167, 0]], ![![-8851, 2672, 167], ![668, -334, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-14, 1, 0]]], ![![![-53, 16, 1]], ![![4, -2, 1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [114, 68, 153, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 78, 101], [137, 94, 72], [0, 1]]
 g := ![![[42, 143, 55], [47, 57], [99, 41, 163], [82, 96, 100], [9, 57], [159, 20, 1], []], ![[77, 24, 8, 156], [76, 9], [138, 1, 32, 26], [95, 168, 150, 46], [57, 140], [86, 69, 50, 102], [66, 167]], ![[19, 123, 21, 26], [153, 37], [40, 56, 16, 107], [140, 129, 69, 103], [94, 136], [86, 106, 131, 12], [95, 167]]]
 h' := ![![[56, 78, 101], [129, 37, 125], [132, 48, 149], [167, 145, 110], [149, 26, 163], [39, 56, 149], [0, 0, 1], [0, 1]], ![[137, 94, 72], [35, 46, 90], [7, 75, 170], [146, 57, 73], [159, 110, 129], [16, 7, 113], [110, 88, 94], [56, 78, 101]], ![[0, 1], [55, 90, 131], [71, 50, 27], [123, 144, 163], [95, 37, 54], [36, 110, 84], [154, 85, 78], [137, 94, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 81], []]
 b := ![[], [127, 160, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [114, 68, 153, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3112962, 3390108, -6331800]
  a := ![11, 12, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17994, 19596, -36600]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [176, 56, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 34, 135], [108, 144, 44], [0, 1]]
 g := ![![[140, 40, 153], [148, 122, 95], [132, 56], [76, 138], [66, 61, 48], [25, 170, 1], []], ![[75, 23, 11, 107], [81, 169, 152, 36], [95, 75], [14, 126], [138, 105, 158, 45], [2, 174, 88, 158], [169, 146]], ![[113, 71, 143, 111], [165, 111, 81, 113], [133, 89], [172, 95], [35, 150, 163, 92], [93, 10, 20, 28], [81, 146]]]
 h' := ![![[62, 34, 135], [86, 160, 137], [57, 108, 128], [52, 160, 134], [19, 143, 106], [75, 5, 103], [0, 0, 1], [0, 1]], ![[108, 144, 44], [178, 178, 158], [10, 172, 76], [158, 109, 84], [37, 140, 22], [143, 33, 113], [55, 23, 144], [62, 34, 135]], ![[0, 1], [35, 20, 63], [176, 78, 154], [80, 89, 140], [82, 75, 51], [170, 141, 142], [93, 156, 34], [108, 144, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166, 49], []]
 b := ![[], [86, 156, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [176, 56, 9, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![284968, 97913, -805321]
  a := ![5, 4, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1592, 547, -4499]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 0, -1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![33, 0, -1]] 
 ![![181, 0, 0], ![1, 1, 0], ![148, 0, 1]] where
  M :=![![![33, 0, -1], ![-6, 10, -5], ![5, -11, 5]]]
  hmulB := by decide  
  f := ![![![5, -11, -10]], ![![0, -1, -1]], ![![4, -11, -10]]]
  g := ![![![1, 0, -1], ![4, 10, -5], ![-4, -11, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, -1, 1]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-16, -1, 1]] 
 ![![181, 0, 0], ![16, 1, 0], ![0, 0, 1]] where
  M :=![![![-16, -1, 1], ![11, 12, -6], ![-11, -12, 7]]]
  hmulB := by decide  
  f := ![![![-12, 5, 6]], ![![-1, 1, 1]], ![![0, 1, 1]]]
  g := ![![![0, -1, 1], ![-1, 12, -6], ![1, -12, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![17, -1, 0]] 
 ![![181, 0, 0], ![164, 1, 0], ![163, 0, 1]] where
  M :=![![![17, -1, 0], ![5, 22, -11], ![-6, -23, 12]]]
  hmulB := by decide  
  f := ![![![11, 12, 11]], ![![10, 12, 11]], ![![10, 13, 12]]]
  g := ![![![1, -1, 0], ![-10, 22, -11], ![10, -23, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![33, 0, -1]] ![![-16, -1, 1]]
  ![![-517, -21, 26]] where
 M := ![![![-517, -21, 26]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![-517, -21, 26]] ![![17, -1, 0]]
  ![![181, 0, 0]] where
 M := ![![![-9050, -543, 543]]]
 hmul := by decide  
 g := ![![![![-50, -3, 3]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)


lemma PB183I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 182 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 182 (by omega)

def PB183I3 : PrimesBelowBoundCertificateInterval O 137 182 183 where
  m := 9
  g := ![1, 3, 1, 3, 1, 3, 1, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB183I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
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
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![181, 181, 181]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
  β := ![I149N0, I149N1, I149N2, I157N0, I157N1, I157N2, I167N0, I167N1, I167N2, I181N0, I181N1, I181N2]
  Il := ![[], [I149N0, I149N1, I149N2], [], [I157N0, I157N1, I157N2], [], [I167N0, I167N1, I167N2], [], [], [I181N0, I181N1, I181N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
