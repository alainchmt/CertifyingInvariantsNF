
import IdealArithmetic.Examples.NF3_1_853335_1.RI3_1_853335_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![11, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![11, 1, 0]] 
 ![![139, 0, 0], ![11, 1, 0], ![109, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![11, 1, 0], ![6, 8, 12], ![180, 4, 14]]]
  hmulB := by decide  
  f := ![![![2715, 3646, 5472], ![278, -63384, 0]], ![![205, 287, 432], ![140, -5004, 0]], ![![2128, 2859, 4291], ![231, -49704, 0]]]
  g := ![![![1, 0, 0], ![-11, 139, 0], ![-109, 0, 139]], ![![0, 1, 0], ![-10, 8, 12], ![-10, 4, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![35, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![35, 1, 0]] 
 ![![139, 0, 0], ![35, 1, 0], ![23, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![35, 1, 0], ![6, 32, 12], ![180, 4, 38]]]
  hmulB := by decide  
  f := ![![![1914, 11131, 4176], ![695, -48372, 0]], ![![452, 2782, 1044], ![279, -12093, 0]], ![![288, 1841, 691], ![229, -8004, 0]]]
  g := ![![![1, 0, 0], ![-35, 139, 0], ![-23, 0, 139]], ![![0, 1, 0], ![-10, 32, 12], ![-6, 4, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-46, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-46, 1, 0]] 
 ![![139, 0, 0], ![93, 1, 0], ![137, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-46, 1, 0], ![6, -49, 12], ![180, 4, -43]]]
  hmulB := by decide  
  f := ![![![-1309, 12197, -2988], ![556, 34611, 0]], ![![-857, 8131, -1992], ![418, 23074, 0]], ![![-1267, 12021, -2945], ![618, 34113, 0]]]
  g := ![![![1, 0, 0], ![-93, 139, 0], ![-137, 0, 139]], ![![-1, 1, 0], ![21, -49, 12], ![41, 4, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![11, 1, 0]] ![![139, 0, 0], ![35, 1, 0]]
  ![![139, 0, 0], ![21, -8, 1]] where
 M := ![![![19321, 0, 0], ![4865, 139, 0]], ![![1529, 139, 0], ![391, 43, 12]]]
 hmul := by decide  
 g := ![![![![118, 8, -1], ![139, 0, 0]], ![![14, 9, -1], ![139, 0, 0]]], ![![![-10, 9, -1], ![139, 0, 0]], ![![1, 1, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![21, -8, 1]] ![![139, 0, 0], ![-46, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-6394, 139, 0]], ![![2919, -1112, 139], ![-834, 417, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-46, 1, 0]]], ![![![21, -8, 1]], ![![-6, 3, -1]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-27, 71, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-27, 71, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![122, 71, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-27, 71, 1], ![606, -236, 855], ![12872, 300, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-122, -71, 149]], ![![-1, 0, 1], ![-696, -409, 855], ![-70, -89, 191]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [85, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 148], [0, 1]]
 g := ![![[127, 142], [123], [123, 22], [1], [44, 76], [19], [1]], ![[0, 7], [123], [139, 127], [1], [18, 73], [19], [1]]]
 h' := ![![[82, 148], [4, 69], [124, 102], [140, 52], [134, 1], [97, 134], [64, 82], [0, 1]], ![[0, 1], [0, 80], [144, 47], [83, 97], [67, 148], [59, 15], [83, 67], [82, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [126, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [85, 67, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1051, 586, -210]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![179, 104, -210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![39, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![39, 1, 0]] 
 ![![149, 0, 0], ![39, 1, 0], ![107, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![39, 1, 0], ![6, 36, 12], ![180, 4, 42]]]
  hmulB := by decide  
  f := ![![![79633, 516004, 172056], ![24436, -2136362, 0]], ![![20835, 135029, 45024], ![6408, -559048, 0]], ![![57178, 370553, 123557], ![17579, -1534166, 0]]]
  g := ![![![1, 0, 0], ![-39, 149, 0], ![-107, 0, 149]], ![![0, 1, 0], ![-18, 36, 12], ![-30, 4, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-27, 71, 1]] ![![149, 0, 0], ![39, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![5811, 149, 0]], ![![-4023, 10579, 149], ![-447, 2533, 894]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![39, 1, 0]]], ![![![-27, 71, 1]], ![![-3, 17, 6]]]]
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
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-64, 44, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-64, 44, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![87, 44, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-64, 44, 1], ![444, -192, 531], ![8012, 192, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -44, 151]], ![![-1, 0, 1], ![-303, -156, 531], ![11, -20, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [81, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 150], [0, 1]]
 g := ![![[79, 110], [8, 116], [2, 32], [2], [87, 124], [78], [1]], ![[0, 41], [40, 35], [141, 119], [2], [116, 27], [78], [1]]]
 h' := ![![[94, 150], [107, 84], [140, 56], [73, 118], [50, 105], [92, 107], [70, 94], [0, 1]], ![[0, 1], [0, 67], [119, 95], [142, 33], [105, 46], [33, 44], [148, 57], [94, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [61, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [81, 57, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2737, 400, 668]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-403, -192, 668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![73, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![73, 1, 0]] 
 ![![151, 0, 0], ![73, 1, 0], ![78, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![73, 1, 0], ![6, 70, 12], ![180, 4, 76]]]
  hmulB := by decide  
  f := ![![![17644, 264531, 45360], ![10419, -570780, 0]], ![![8553, 127857, 21924], ![4984, -275877, 0]], ![![9103, 136645, 23431], ![5405, -294840, 0]]]
  g := ![![![1, 0, 0], ![-73, 151, 0], ![-78, 0, 151]], ![![0, 1, 0], ![-40, 70, 12], ![-40, 4, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-64, 44, 1]] ![![151, 0, 0], ![73, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![11023, 151, 0]], ![![-9664, 6644, 151], ![-4228, 3020, 604]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![73, 1, 0]]], ![![![-64, 44, 1]], ![![-28, 20, 4]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![10, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![10, 1, 0]] 
 ![![157, 0, 0], ![10, 1, 0], ![47, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![10, 1, 0], ![6, 7, 12], ![180, 4, 13]]]
  hmulB := by decide  
  f := ![![![74241, 86976, 149160], ![5338, -1951510, 0]], ![![4716, 5534, 9492], ![472, -124187, 0]], ![![22221, 26037, 44653], ![1661, -584210, 0]]]
  g := ![![![1, 0, 0], ![-10, 157, 0], ![-47, 0, 157]], ![![0, 1, 0], ![-4, 7, 12], ![-3, 4, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![45, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![45, 1, 0]] 
 ![![157, 0, 0], ![45, 1, 0], ![0, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![45, 1, 0], ![6, 42, 12], ![180, 4, 48]]]
  hmulB := by decide  
  f := ![![![-44, -1, 0], ![157, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-27, -39, -11], ![75, 144, 0]]]
  g := ![![![1, 0, 0], ![-45, 157, 0], ![0, 0, 157]], ![![0, 1, 0], ![-12, 42, 12], ![0, 4, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-55, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-55, 1, 0]] 
 ![![157, 0, 0], ![102, 1, 0], ![101, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-55, 1, 0], ![6, -58, 12], ![180, 4, -52]]]
  hmulB := by decide  
  f := ![![![27277, -301876, 62472], ![-11304, -817342, 0]], ![![17708, -196109, 40584], ![-7378, -530974, 0]], ![![17521, -194200, 40189], ![-7348, -525806, 0]]]
  g := ![![![1, 0, 0], ![-102, 157, 0], ![-101, 0, 157]], ![![-1, 1, 0], ![30, -58, 12], ![32, 4, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![10, 1, 0]] ![![157, 0, 0], ![45, 1, 0]]
  ![![157, 0, 0], ![38, -48, 1]] where
 M := ![![![24649, 0, 0], ![7065, 157, 0]], ![![1570, 157, 0], ![456, 52, 12]]]
 hmul := by decide  
 g := ![![![![119, 48, -1], ![157, 0, 0]], ![![7, 49, -1], ![157, 0, 0]]], ![![![-28, 49, -1], ![157, 0, 0]], ![![0, 4, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![38, -48, 1]] ![![157, 0, 0], ![-55, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-8635, 157, 0]], ![![5966, -7536, 157], ![-2198, 2826, -628]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-55, 1, 0]]], ![![![38, -48, 1]], ![![-14, 18, -4]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [50, 135, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 13, 101], [161, 149, 62], [0, 1]]
 g := ![![[19, 5, 65], [161, 143, 146], [80, 133], [70, 134], [19, 97], [52, 26, 1], []], ![[102, 133, 140, 120], [154, 124, 70, 98], [157, 16], [1, 34], [33, 55], [77, 19, 116, 73], [43, 95]], ![[109, 83, 89, 126], [62, 3, 63, 6], [126, 155], [137, 96], [135, 54], [13, 139, 103, 46], [82, 95]]]
 h' := ![![[28, 13, 101], [100, 47, 126], [9, 30, 132], [74, 30, 123], [92, 134, 42], [8, 156, 74], [0, 0, 1], [0, 1]], ![[161, 149, 62], [124, 68, 49], [0, 54, 41], [134, 151, 4], [99, 94, 69], [114, 17, 50], [101, 116, 149], [28, 13, 101]], ![[0, 1], [131, 48, 151], [111, 79, 153], [39, 145, 36], [83, 98, 52], [98, 153, 39], [142, 47, 13], [161, 149, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 152], []]
 b := ![[], [95, 31, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [50, 135, 137, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-968900851, -44615219, -45654018]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5944177, -273713, -280086]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-23, 8, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-23, 8, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![144, 8, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-23, 8, 1], ![228, -43, 99], ![1532, 48, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-144, -8, 167]], ![![-1, 0, 1], ![-84, -5, 99], ![4, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [63, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 166], [0, 1]]
 g := ![![[106, 114], [101, 33], [86, 124], [2], [130], [90, 4], [1]], ![[0, 53], [0, 134], [0, 43], [2], [130], [98, 163], [1]]]
 h' := ![![[2, 166], [150, 92], [93, 37], [117, 25], [57, 154], [8, 56], [104, 2], [0, 1]], ![[0, 1], [0, 75], [0, 130], [0, 142], [31, 13], [120, 111], [108, 165], [2, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [101, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [63, 165, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2795, 1524, -1062]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![899, 60, -1062]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![68, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![68, 1, 0]] 
 ![![167, 0, 0], ![68, 1, 0], ![161, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![68, 1, 0], ![6, 65, 12], ![180, 4, 71]]]
  hmulB := by decide  
  f := ![![![72241, 937090, 173040], ![35070, -2408140, 0]], ![![29378, 381529, 70452], ![14363, -980457, 0]], ![![69639, 903422, 166823], ![33826, -2321620, 0]]]
  g := ![![![1, 0, 0], ![-68, 167, 0], ![-161, 0, 167]], ![![0, 1, 0], ![-38, 65, 12], ![-69, 4, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-23, 8, 1]] ![![167, 0, 0], ![68, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![11356, 167, 0]], ![![-3841, 1336, 167], ![-1336, 501, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![68, 1, 0]]], ![![![-23, 8, 1]], ![![-8, 3, 1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-36, 42, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-36, 42, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![137, 42, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-36, 42, 1], ![432, -158, 507], ![7652, 184, 95]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-137, -42, 173]], ![![-1, 0, 1], ![-399, -124, 507], ![-31, -22, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [87, 170, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 172], [0, 1]]
 g := ![![[167, 52], [92], [102, 90], [25, 122], [38], [24, 9], [1]], ![[150, 121], [92], [26, 83], [45, 51], [38], [51, 164], [1]]]
 h' := ![![[3, 172], [133, 15], [122, 28], [74, 69], [125, 45], [161, 111], [86, 3], [0, 1]], ![[0, 1], [5, 158], [33, 145], [108, 104], [87, 128], [148, 62], [95, 170], [3, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [124, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [87, 170, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![744, 689, -828]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![660, 205, -828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![12, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![12, 1, 0]] 
 ![![173, 0, 0], ![12, 1, 0], ![78, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![12, 1, 0], ![6, 9, 12], ![180, 4, 15]]]
  hmulB := by decide  
  f := ![![![30739, 46345, 61812], ![2422, -891123, 0]], ![![2130, 3212, 4284], ![174, -61761, 0]], ![![13854, 20895, 27869], ![1167, -401778, 0]]]
  g := ![![![1, 0, 0], ![-12, 173, 0], ![-78, 0, 173]], ![![0, 1, 0], ![-6, 9, 12], ![-6, 4, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-36, 42, 1]] ![![173, 0, 0], ![12, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![2076, 173, 0]], ![![-6228, 7266, 173], ![0, 346, 519]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![12, 1, 0]]], ![![![-36, 42, 1]], ![![0, 2, 3]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![83, 20, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![83, 20, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![83, 20, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![83, 20, 1], ![300, 27, 243], ![3692, 96, 148]]]
  hmulB := by decide  
  f := ![![![-82, -20, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -20, 179]], ![![0, 0, 1], ![-111, -27, 243], ![-48, -16, 148]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [79, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 178], [0, 1]]
 g := ![![[140, 107], [106, 101], [61], [93], [57, 89], [1, 12], [1]], ![[89, 72], [6, 78], [61], [93], [38, 90], [99, 167], [1]]]
 h' := ![![[38, 178], [39, 69], [34, 82], [60, 47], [151, 123], [100, 140], [100, 38], [0, 1]], ![[0, 1], [155, 110], [107, 97], [56, 132], [171, 56], [50, 39], [112, 141], [38, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [67, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [79, 141, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![158299, 29052, 16954]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6977, -1732, 16954]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-64, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-64, 1, 0]] 
 ![![179, 0, 0], ![115, 1, 0], ![31, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-64, 1, 0], ![6, -67, 12], ![180, 4, -61]]]
  hmulB := by decide  
  f := ![![![135621, -1746365, 312840], ![-58175, -4666530, 0]], ![![87113, -1121907, 200976], ![-37410, -2997892, 0]], ![![23545, -302444, 54179], ![-9914, -808170, 0]]]
  g := ![![![1, 0, 0], ![-115, 179, 0], ![-31, 0, 179]], ![![-1, 1, 0], ![41, -67, 12], ![9, 4, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![83, 20, 1]] ![![179, 0, 0], ![-64, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-11456, 179, 0]], ![![14857, 3580, 179], ![-5012, -1253, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-64, 1, 0]]], ![![![83, 20, 1]], ![![-28, -7, 1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [114, 155, 172, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 138, 139], [6, 42, 42], [0, 1]]
 g := ![![[100, 166, 81], [132, 125], [132, 82, 4], [72, 169], [162, 43, 9], [107, 9, 1], []], ![[78, 136, 154, 73], [1, 170], [38, 169, 19, 60], [50, 62], [132, 119, 2, 29], [25, 129, 70, 122], [121, 135]], ![[0, 154, 142, 25], [34, 11], [88, 141, 50, 46], [114, 170], [58, 50, 81, 126], [95, 33, 13, 9], [37, 135]]]
 h' := ![![[3, 138, 139], [57, 19, 9], [156, 62, 46], [154, 79, 179], [175, 7, 168], [110, 127, 178], [0, 0, 1], [0, 1]], ![[6, 42, 42], [34, 152, 123], [94, 175, 52], [87, 68, 37], [30, 49, 65], [35, 8, 151], [152, 168, 42], [3, 138, 139]], ![[0, 1], [0, 10, 49], [16, 125, 83], [123, 34, 146], [102, 125, 129], [24, 46, 33], [162, 13, 138], [6, 42, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [159, 157], []]
 b := ![[], [52, 36, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [114, 155, 172, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![89052, 4706, 5068]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![492, 26, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![73, -31, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![73, -31, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![73, 160, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![73, -31, 1], ![-6, 170, -369], ![-5488, -108, -15]]]
  hmulB := by decide  
  f := ![![![-72, 31, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -160, 191]], ![![0, -1, 1], ![141, 310, -369], ![-23, 12, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [82, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 190], [0, 1]]
 g := ![![[169, 180], [46, 46], [188, 115], [186, 90], [36, 163], [63, 158], [1]], ![[189, 11], [136, 145], [31, 76], [5, 101], [139, 28], [123, 33], [1]]]
 h' := ![![[85, 190], [48, 107], [55, 76], [28, 146], [104, 89], [182, 78], [109, 85], [0, 1]], ![[0, 1], [166, 84], [21, 115], [23, 45], [29, 102], [127, 113], [76, 106], [85, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [95, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [82, 106, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2661, 1196, 1588]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-593, -1324, 1588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-13, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-13, 1, 0]] 
 ![![191, 0, 0], ![178, 1, 0], ![15, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-13, 1, 0], ![6, -16, 12], ![180, 4, -10]]]
  hmulB := by decide  
  f := ![![![27050, -72501, 54384], ![-2101, -865612, 0]], ![![25209, -67558, 50676], ![-1909, -806593, 0]], ![![2127, -5694, 4271], ![-126, -67980, 0]]]
  g := ![![![1, 0, 0], ![-178, 191, 0], ![-15, 0, 191]], ![![-1, 1, 0], ![14, -16, 12], ![-2, 4, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![73, -31, 1]] ![![191, 0, 0], ![-13, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-2483, 191, 0]], ![![13943, -5921, 191], ![-955, 573, -382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-13, 1, 0]]], ![![![73, -31, 1]], ![![-5, 3, -2]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![1, -67, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![1, -67, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![1, 126, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![1, -67, 1], ![-222, 206, -801], ![-11968, -252, -195]]]
  hmulB := by decide  
  f := ![![![0, 67, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -126, 193]], ![![0, -1, 1], ![3, 524, -801], ![-61, 126, -195]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [166, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [128, 192], [0, 1]]
 g := ![![[162, 50], [32], [86], [191], [86], [36], [128, 1]], ![[0, 143], [32], [86], [191], [86], [36], [63, 192]]]
 h' := ![![[128, 192], [84, 126], [68, 178], [107, 146], [136, 159], [138, 146], [175, 6], [0, 1]], ![[0, 1], [0, 67], [78, 15], [74, 47], [30, 34], [105, 47], [171, 187], [128, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [17, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [166, 65, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2166, 400, -150]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 100, -150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![29, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![29, 1, 0]] 
 ![![193, 0, 0], ![29, 1, 0], ![2, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![29, 1, 0], ![6, 26, 12], ![180, 4, 32]]]
  hmulB := by decide  
  f := ![![![-18015, -80064, -36960], ![-3088, 594440, 0]], ![![-2714, -12010, -5544], ![-385, 89166, 0]], ![![-196, -830, -383], ![30, 6160, 0]]]
  g := ![![![1, 0, 0], ![-29, 193, 0], ![-2, 0, 193]], ![![0, 1, 0], ![-4, 26, 12], ![0, 4, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![1, -67, 1]] ![![193, 0, 0], ![29, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![5597, 193, 0]], ![![193, -12931, 193], ![-193, -1737, -772]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![29, 1, 0]]], ![![![1, -67, 1]], ![![-1, -9, -4]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB262I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB262I3 : PrimesBelowBoundCertificateInterval O 137 193 262 where
  m := 11
  g := ![3, 2, 2, 3, 1, 2, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB262I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N0, I139N1, I139N2, I149N1, I151N1, I157N0, I157N1, I157N2, I167N1, I173N1, I179N1, I191N1, I193N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N1], [I157N0, I157N1, I157N2], [], [I167N1], [I173N1], [I179N1], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
