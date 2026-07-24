
import IdealArithmetic.Examples.NF3_1_538412_3.RI3_1_538412_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6647, 51, -302]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![6647, 51, -302]] 
 ![![139, 0, 0], ![0, 139, 0], ![30, 50, 1]] where
  M :=![![![6647, 51, -302], ![-44798, 3223, -94], ![-9666, -4573, 3125]]]
  hmulB := by decide  
  f := ![![![69367, 8789, 6968]], ![![1013686, 128437, 101826]], ![![391822, 49645, 39359]]]
  g := ![![![113, 109, -302], ![-302, 57, -94], ![-744, -1157, 3125]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [121, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 138], [0, 1]]
 g := ![![[10, 54], [102, 106], [41], [120, 47], [77], [13], [1]], ![[0, 85], [0, 33], [41], [101, 92], [77], [13], [1]]]
 h' := ![![[41, 138], [29, 101], [108, 55], [75, 67], [0, 73], [2, 63], [18, 41], [0, 1]], ![[0, 1], [0, 38], [0, 84], [42, 72], [74, 66], [83, 76], [31, 98], [41, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [43, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [121, 98, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1645, 425, -200]
  a := ![1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, 75, -200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69367, 8789, 6968]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![69367, 8789, 6968]] 
 ![![139, 0, 0], ![54, 1, 0], ![136, 0, 1]] where
  M :=![![![69367, 8789, 6968], ![1013686, 128437, 101826], ![1697948, 215135, 170561]]]
  hmulB := by decide  
  f := ![![![6647, 51, -302]], ![![2260, 43, -118]], ![![6434, 17, -273]]]
  g := ![![![-9733, 8789, 6968], ![-142232, 128437, 101826], ![-238242, 215135, 170561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![6647, 51, -302]] ![![69367, 8789, 6968]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-81, 14, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-81, 14, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![68, 14, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-81, 14, 1], ![120, -98, 142], ![2129, 171, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -14, 149]], ![![-1, 0, 1], ![-64, -14, 142], ![33, 5, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [103, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 148], [0, 1]]
 g := ![![[119, 68], [76], [17, 125], [67], [16, 96], [31], [1]], ![[0, 81], [76], [59, 24], [67], [146, 53], [31], [1]]]
 h' := ![![[110, 148], [97, 98], [37, 134], [34, 107], [140, 31], [115, 120], [46, 110], [0, 1]], ![[0, 1], [0, 51], [26, 15], [33, 42], [123, 118], [54, 29], [77, 39], [110, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [101, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [103, 39, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9603, 1577, 2784]
  a := ![-3, -5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1335, -251, 2784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![7, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![7, 1, 0]] 
 ![![149, 0, 0], ![7, 1, 0], ![41, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![7, 1, 0], ![-2, 5, 10], ![148, 11, 9]]]
  hmulB := by decide  
  f := ![![![-15466, 38723, 77440], ![-447, -1153856, 0]], ![![-726, 1815, 3630], ![1, -54087, 0]], ![![-4258, 10655, 21309], ![-75, -317504, 0]]]
  g := ![![![1, 0, 0], ![-7, 149, 0], ![-41, 0, 149]], ![![0, 1, 0], ![-3, 5, 10], ![-2, 11, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-81, 14, 1]] ![![149, 0, 0], ![7, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![1043, 149, 0]], ![![-12069, 2086, 149], ![-447, 0, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![7, 1, 0]]], ![![![-81, 14, 1]], ![![-3, 0, 1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![58, 26, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![58, 26, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![58, 26, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![58, 26, 1], ![96, 17, 262], ![3905, 303, 122]]]
  hmulB := by decide  
  f := ![![![-57, -26, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -26, 151]], ![![0, 0, 1], ![-100, -45, 262], ![-21, -19, 122]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [92, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 150], [0, 1]]
 g := ![![[2, 78], [138, 91], [93, 1], [69], [109, 32], [32], [1]], ![[146, 73], [4, 60], [60, 150], [69], [110, 119], [32], [1]]]
 h' := ![![[118, 150], [139, 94], [51, 53], [63, 1], [89, 62], [84, 33], [59, 118], [0, 1]], ![[0, 1], [57, 57], [114, 98], [30, 150], [6, 89], [52, 118], [91, 33], [118, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [112, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [92, 33, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![230647, 77963, 54205]
  a := ![1, 2, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19293, -8817, 54205]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![40, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![40, 1, 0]] 
 ![![151, 0, 0], ![40, 1, 0], ![29, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![40, 1, 0], ![-2, 38, 10], ![148, 11, 42]]]
  hmulB := by decide  
  f := ![![![-6831, 134374, 35360], ![-906, -533936, 0]], ![![-1832, 35569, 9360], ![-150, -141336, 0]], ![![-1349, 25806, 6791], ![-34, -102544, 0]]]
  g := ![![![1, 0, 0], ![-40, 151, 0], ![-29, 0, 151]], ![![0, 1, 0], ![-12, 38, 10], ![-10, 11, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![58, 26, 1]] ![![151, 0, 0], ![40, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![6040, 151, 0]], ![![8758, 3926, 151], ![2416, 1057, 302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![40, 1, 0]]], ![![![58, 26, 1]], ![![16, 7, 2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![34, -42, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![34, -42, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![34, 115, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![34, -42, 1], ![232, 129, -418], ![-6159, -445, -38]]]
  hmulB := by decide  
  f := ![![![-33, 42, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -115, 157]], ![![0, -1, 1], ![92, 307, -418], ![-31, 25, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [134, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 156], [0, 1]]
 g := ![![[29, 138], [12], [39, 100], [37, 81], [116, 30], [108], [1]], ![[73, 19], [12], [14, 57], [56, 76], [30, 127], [108], [1]]]
 h' := ![![[39, 156], [103, 83], [112, 13], [66, 10], [156, 148], [30, 40], [23, 39], [0, 1]], ![[0, 1], [43, 74], [148, 144], [142, 147], [119, 9], [20, 117], [131, 118], [39, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [136, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [134, 118, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4939, 2564, 552]
  a := ![3, 4, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-151, -388, 552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-53, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-53, 1, 0]] 
 ![![157, 0, 0], ![104, 1, 0], ![38, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-53, 1, 0], ![-2, -55, 10], ![148, 11, -51]]]
  hmulB := by decide  
  f := ![![![-6712, -194817, 35420], ![1099, -556094, 0]], ![![-4426, -129035, 23460], ![786, -368322, 0]], ![![-1580, -47154, 8573], ![398, -134596, 0]]]
  g := ![![![1, 0, 0], ![-104, 157, 0], ![-38, 0, 157]], ![![-1, 1, 0], ![34, -55, 10], ![6, 11, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![34, -42, 1]] ![![157, 0, 0], ![-53, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-8321, 157, 0]], ![![5338, -6594, 157], ![-1570, 2355, -471]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-53, 1, 0]]], ![![![34, -42, 1]], ![![-10, 15, -3]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![52, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![52, 1, 0]] 
 ![![163, 0, 0], ![52, 1, 0], ![131, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![52, 1, 0], ![-2, 50, 10], ![148, 11, 54]]]
  hmulB := by decide  
  f := ![![![13889, -365414, -73080], ![2282, 1191204, 0]], ![![4402, -116555, -23310], ![816, 379953, 0]], ![![11177, -293676, -58733], ![1788, 957348, 0]]]
  g := ![![![1, 0, 0], ![-52, 163, 0], ![-131, 0, 163]], ![![0, 1, 0], ![-24, 50, 10], ![-46, 11, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-49, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-49, 1, 0]] 
 ![![163, 0, 0], ![114, 1, 0], ![27, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-49, 1, 0], ![-2, -51, 10], ![148, 11, -47]]]
  hmulB := by decide  
  f := ![![![18238, 483801, -94860], ![-2445, 1546218, 0]], ![![12779, 338344, -66340], ![-1629, 1081342, 0]], ![![3061, 80138, -15713], ![-272, 256122, 0]]]
  g := ![![![1, 0, 0], ![-114, 163, 0], ![-27, 0, 163]], ![![-1, 1, 0], ![34, -51, 10], ![1, 11, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-3, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-3, 1, 0]] 
 ![![163, 0, 0], ![160, 1, 0], ![145, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-3, 1, 0], ![-2, -5, 10], ![148, 11, -1]]]
  hmulB := by decide  
  f := ![![![-2048, -5131, 10260], ![163, -167238, 0]], ![![-2010, -5036, 10070], ![164, -164141, 0]], ![![-1823, -4564, 9127], ![82, -148770, 0]]]
  g := ![![![1, 0, 0], ![-160, 163, 0], ![-145, 0, 163]], ![![-1, 1, 0], ![-4, -5, 10], ![-9, 11, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![52, 1, 0]] ![![163, 0, 0], ![-49, 1, 0]]
  ![![163, 0, 0], ![71, 49, 1]] where
 M := ![![![26569, 0, 0], ![-7987, 163, 0]], ![![8476, 163, 0], ![-2550, 1, 10]]]
 hmul := by decide  
 g := ![![![![92, -49, -1], ![163, 0, 0]], ![![-49, 1, 0], ![0, 0, 0]]], ![![![-19, -48, -1], ![163, 0, 0]], ![![-20, -3, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![71, 49, 1]] ![![163, 0, 0], ![-3, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-489, 163, 0]], ![![11573, 7987, 163], ![-163, -163, 489]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-3, 1, 0]]], ![![![71, 49, 1]], ![![-1, -1, 3]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129, -18, 16]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-129, -18, 16]] 
 ![![167, 0, 0], ![0, 167, 0], ![65, 145, 1]] where
  M :=![![![-129, -18, 16], ![2404, 83, -148], ![-1752, 74, 27]]]
  hmulB := by decide  
  f := ![![![-79, -10, -8]], ![![-1164, -147, -116]], ![![-1053, -133, -105]]]
  g := ![![![-7, -14, 16], ![72, 129, -148], ![-21, -23, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [141, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 166], [0, 1]]
 g := ![![[2, 122], [34, 154], [95, 62], [19], [107], [26, 32], [1]], ![[0, 45], [26, 13], [146, 105], [19], [107], [20, 135], [1]]]
 h' := ![![[52, 166], [49, 150], [132, 133], [42, 88], [7, 55], [8, 21], [26, 52], [0, 1]], ![[0, 1], [0, 17], [34, 34], [109, 79], [28, 112], [98, 146], [58, 115], [52, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [133, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [141, 115, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1682, 425, -285]
  a := ![1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![121, 250, -285]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 10, 8]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![79, 10, 8]] 
 ![![167, 0, 0], ![51, 1, 0], ![134, 0, 1]] where
  M :=![![![79, 10, 8], ![1164, 147, 116], ![1936, 246, 195]]]
  hmulB := by decide  
  f := ![![![129, 18, -16]], ![![25, 5, -4]], ![![114, 14, -13]]]
  g := ![![![-9, 10, 8], ![-131, 147, 116], ![-220, 246, 195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-129, -18, 16]] ![![79, 10, 8]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-78, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-78, 1, 0]] 
 ![![173, 0, 0], ![95, 1, 0], ![137, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-78, 1, 0], ![-2, -80, 10], ![148, 11, -76]]]
  hmulB := by decide  
  f := ![![![-11021, -481453, 60180], ![2249, -1041114, 0]], ![![-6061, -264327, 33040], ![1212, -571592, 0]], ![![-8669, -381267, 47657], ![1911, -824466, 0]]]
  g := ![![![1, 0, 0], ![-95, 173, 0], ![-137, 0, 173]], ![![-1, 1, 0], ![36, -80, 10], ![55, 11, -76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-57, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-57, 1, 0]] 
 ![![173, 0, 0], ![116, 1, 0], ![96, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-57, 1, 0], ![-2, -59, 10], ![148, 11, -55]]]
  hmulB := by decide  
  f := ![![![-23266, -721709, 122320], ![3633, -2116136, 0]], ![![-15603, -483873, 82010], ![2423, -1418773, 0]], ![![-12906, -400486, 67877], ![2030, -1174272, 0]]]
  g := ![![![1, 0, 0], ![-116, 173, 0], ![-96, 0, 173]], ![![-1, 1, 0], ![34, -59, 10], ![24, 11, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-38, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-38, 1, 0]] 
 ![![173, 0, 0], ![135, 1, 0], ![90, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-38, 1, 0], ![-2, -40, 10], ![148, 11, -36]]]
  hmulB := by decide  
  f := ![![![20175, 411851, -102960], ![-1903, 1781208, 0]], ![![15727, 321369, -80340], ![-1556, 1389882, 0]], ![![10486, 214258, -53563], ![-1034, 926640, 0]]]
  g := ![![![1, 0, 0], ![-135, 173, 0], ![-90, 0, 173]], ![![-1, 1, 0], ![26, -40, 10], ![11, 11, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-78, 1, 0]] ![![173, 0, 0], ![-57, 1, 0]]
  ![![173, 0, 0], ![-40, -31, 1]] where
 M := ![![![29929, 0, 0], ![-9861, 173, 0]], ![![-13494, 173, 0], ![4444, -137, 10]]]
 hmul := by decide  
 g := ![![![![173, 0, 0], ![0, 0, 0]], ![![-17, 32, -1], ![173, 0, 0]]], ![![![-38, 32, -1], ![173, 0, 0]], ![![28, 1, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-40, -31, 1]] ![![173, 0, 0], ![-38, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-6574, 173, 0]], ![![-6920, -5363, 173], ![1730, 1211, -346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-38, 1, 0]]], ![![![-40, -31, 1]], ![![10, 7, -2]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [122, 63, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 55, 40], [87, 123, 139], [0, 1]]
 g := ![![[161, 30, 56], [58, 144, 61], [156, 17], [64, 110], [90, 97, 172], [83, 135, 1], []], ![[65, 15, 103, 114], [106, 57, 74, 90], [23, 16], [59, 77], [159, 98, 98, 79], [124, 144, 168, 140], [51, 168]], ![[176, 124, 36, 121], [63, 112, 7, 64], [169, 100], [61, 15], [53, 17, 55, 172], [135, 147, 53, 4], [131, 168]]]
 h' := ![![[48, 55, 40], [84, 24, 134], [126, 8, 132], [30, 109, 14], [118, 60, 17], [77, 139, 72], [0, 0, 1], [0, 1]], ![[87, 123, 139], [157, 65, 79], [107, 64, 88], [172, 21, 175], [116, 35, 16], [134, 166, 96], [20, 8, 123], [48, 55, 40]], ![[0, 1], [24, 90, 145], [106, 107, 138], [26, 49, 169], [147, 84, 146], [177, 53, 11], [0, 171, 55], [87, 123, 139]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105, 120], []]
 b := ![[], [162, 35, 176], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [122, 63, 44, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15698658, 1997640, 1260876]
  a := ![-1, 18, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![87702, 11160, 7044]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4364, -95, 235]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-4364, -95, 235]] 
 ![![181, 0, 0], ![0, 181, 0], ![127, 15, 1]] where
  M :=![![![-4364, -95, 235], ![34970, -1589, -480], ![-665, 2950, -1734]]]
  hmulB := by decide  
  f := ![![![23046, 2920, 2315]], ![![336780, 42671, 33830]], ![![47197, 5980, 4741]]]
  g := ![![![-189, -20, 235], ![530, 31, -480], ![1213, 160, -1734]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [156, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 180], [0, 1]]
 g := ![![[47, 152], [126], [27, 56], [16], [140, 5], [80, 138], [1]], ![[0, 29], [126], [124, 125], [16], [42, 176], [54, 43], [1]]]
 h' := ![![[89, 180], [121, 141], [132, 137], [139, 31], [61, 177], [9, 154], [25, 89], [0, 1]], ![[0, 1], [0, 40], [17, 44], [2, 150], [67, 4], [140, 27], [163, 92], [89, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [100, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [156, 92, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4835, 428, -68]
  a := ![1, 4, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21, 8, -68]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23046, -2920, -2315]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-23046, -2920, -2315]] 
 ![![181, 0, 0], ![29, 1, 0], ![12, 0, 1]] where
  M :=![![![-23046, -2920, -2315], ![-336780, -42671, -33830], ![-564115, -71475, -56666]]]
  hmulB := by decide  
  f := ![![![4364, 95, -235]], ![![506, 24, -35]], ![![293, -10, -6]]]
  g := ![![![494, -2920, -2315], ![7219, -42671, -33830], ![12092, -71475, -56666]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-4364, -95, 235]] ![![-23046, -2920, -2315]]
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
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![49, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![49, 1, 0]] 
 ![![191, 0, 0], ![49, 1, 0], ![56, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![49, 1, 0], ![-2, 47, 10], ![148, 11, 51]]]
  hmulB := by decide  
  f := ![![![-10313, 249294, 53040], ![-1146, -1013064, 0]], ![![-2671, 63921, 13600], ![-190, -259760, 0]], ![![-3045, 73091, 15551], ![-253, -297024, 0]]]
  g := ![![![1, 0, 0], ![-49, 191, 0], ![-56, 0, 191]], ![![0, 1, 0], ![-15, 47, 10], ![-17, 11, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-30, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-30, 1, 0]] 
 ![![191, 0, 0], ![161, 1, 0], ![133, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-30, 1, 0], ![-2, -32, 10], ![148, 11, -28]]]
  hmulB := by decide  
  f := ![![![-3159, -51522, 16100], ![382, -307510, 0]], ![![-2653, -43426, 13570], ![383, -259187, 0]], ![![-2187, -35877, 11211], ![347, -214130, 0]]]
  g := ![![![1, 0, 0], ![-161, 191, 0], ![-133, 0, 191]], ![![-1, 1, 0], ![20, -32, 10], ![11, 11, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-19, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-19, 1, 0]] 
 ![![191, 0, 0], ![172, 1, 0], ![170, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-19, 1, 0], ![-2, -21, 10], ![148, 11, -17]]]
  hmulB := by decide  
  f := ![![![21, 210, -100], ![0, 1910, 0]], ![![19, 189, -90], ![1, 1719, 0]], ![![36, 186, -89], ![174, 1700, 0]]]
  g := ![![![1, 0, 0], ![-172, 191, 0], ![-170, 0, 191]], ![![-1, 1, 0], ![10, -21, 10], ![6, 11, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![49, 1, 0]] ![![191, 0, 0], ![-30, 1, 0]]
  ![![191, 0, 0], ![82, 59, 1]] where
 M := ![![![36481, 0, 0], ![-5730, 191, 0]], ![![9359, 191, 0], ![-1472, 17, 10]]]
 hmul := by decide  
 g := ![![![![109, -59, -1], ![191, 0, 0]], ![![-30, 1, 0], ![0, 0, 0]]], ![![![-33, -58, -1], ![191, 0, 0]], ![![-12, -3, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![82, 59, 1]] ![![191, 0, 0], ![-19, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-3629, 191, 0]], ![![15662, 11269, 191], ![-1528, -1146, 573]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-19, 1, 0]]], ![![![82, 59, 1]], ![![-8, -6, 3]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-17, 15, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-17, 15, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![176, 15, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-17, 15, 1], ![118, -36, 152], ![2277, 182, 25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-176, -15, 193]], ![![-1, 0, 1], ![-138, -12, 152], ![-11, -1, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [131, 65, 1] where
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
 g := ![![[83, 28], [112], [54], [134], [23], [137], [128, 1]], ![[0, 165], [112], [54], [134], [23], [137], [63, 192]]]
 h' := ![![[128, 192], [143, 118], [95, 43], [118, 132], [63, 110], [145, 122], [23, 41], [0, 1]], ![[0, 1], [0, 75], [2, 150], [30, 61], [54, 83], [128, 71], [60, 152], [128, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [140, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [131, 65, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2743, 1417, 1780]
  a := ![-2, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1609, -131, 1780]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![41, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![41, 1, 0]] 
 ![![193, 0, 0], ![41, 1, 0], ![168, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![41, 1, 0], ![-2, 39, 10], ![148, 11, 43]]]
  hmulB := by decide  
  f := ![![![14774, -295278, -75710], ![1737, 1461203, 0]], ![![3134, -62714, -16080], ![387, 310344, 0]], ![![12842, -257030, -65903], ![1598, 1271928, 0]]]
  g := ![![![1, 0, 0], ![-41, 193, 0], ![-168, 0, 193]], ![![0, 1, 0], ![-17, 39, 10], ![-39, 11, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-17, 15, 1]] ![![193, 0, 0], ![41, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![7913, 193, 0]], ![![-3281, 2895, 193], ![-579, 579, 193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![41, 1, 0]]], ![![![-17, 15, 1]], ![![-3, 3, 1]]]]
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


lemma PB208I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB208I3 : PrimesBelowBoundCertificateInterval O 137 193 208 where
  m := 11
  g := ![2, 2, 2, 2, 3, 2, 3, 1, 2, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB208I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
    · exact ![173, 173, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![191, 191, 191]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
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
  β := ![I139N1, I149N1, I151N1, I157N1, I163N0, I163N1, I163N2, I167N1, I173N0, I173N1, I173N2, I181N1, I191N0, I191N1, I191N2, I193N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1], [I163N0, I163N1, I163N2], [I167N1], [I173N0, I173N1, I173N2], [], [I181N1], [I191N0, I191N1, I191N2], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
