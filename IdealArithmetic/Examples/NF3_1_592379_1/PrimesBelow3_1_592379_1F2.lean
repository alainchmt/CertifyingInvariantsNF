
import IdealArithmetic.Examples.NF3_1_592379_1.RI3_1_592379_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [79, 77, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 7, 58], [80, 75, 25], [0, 1]]
 g := ![![[4, 51, 4], [8, 81, 10], [62, 3], [71, 10], [9, 13, 1], []], ![[34, 20, 24, 46], [70, 53, 35, 2], [1, 64], [41, 81], [26, 42, 65, 60], [56, 44]], ![[64, 74, 42, 75], [3, 59, 3, 64], [32, 25], [58, 78], [64, 36, 44, 63], [6, 44]]]
 h' := ![![[16, 7, 58], [32, 21, 81], [8, 2, 50], [3, 47, 70], [36, 23, 33], [0, 0, 1], [0, 1]], ![[80, 75, 25], [72, 3, 72], [53, 45, 48], [76, 57, 8], [59, 47, 74], [65, 72, 75], [16, 7, 58]], ![[0, 1], [69, 59, 13], [75, 36, 68], [14, 62, 5], [60, 13, 59], [33, 11, 7], [80, 75, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 18], []]
 b := ![[], [2, 30, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [79, 77, 70, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![31125, -8134, -5478]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![375, -98, -66]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [60, 28, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 32, 44], [30, 56, 45], [0, 1]]
 g := ![![[44, 4, 10], [61, 73], [67, 85], [12, 61, 79], [12, 60, 1], []], ![[0, 40, 12, 4], [62, 40], [44, 17], [80, 77, 17, 53], [9, 46, 28, 34], [72, 67]], ![[47, 9, 23, 87], [73, 80], [35, 79], [88, 11, 85, 40], [15, 22, 35, 67], [71, 67]]]
 h' := ![![[30, 32, 44], [76, 4, 59], [49, 44, 47], [81, 73, 21], [81, 69, 48], [0, 0, 1], [0, 1]], ![[30, 56, 45], [1, 76, 9], [28, 18, 29], [49, 5, 27], [60, 84, 28], [51, 67, 56], [30, 32, 44]], ![[0, 1], [70, 9, 21], [0, 27, 13], [63, 11, 41], [3, 25, 13], [22, 22, 32], [30, 56, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 18], []]
 b := ![[], [54, 21, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [60, 28, 29, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![193130, -202831, 52866]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2170, -2279, 594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀


def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-46, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-46, 1, 0]] 
 ![![97, 0, 0], ![51, 1, 0], ![18, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-46, 1, 0], ![0, -46, 1], ![86, -49, -45]]]
  hmulB := by decide  
  f := ![![![1427, -31, 0], ![3007, 0, 0]], ![![829, -18, 0], ![1747, 0, 0]], ![![298, -6, 0], ![628, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 97, 0], ![-18, 0, 97]], ![![-1, 1, 0], ![24, -46, 1], ![35, -49, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-6, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-6, 1, 0]] 
 ![![97, 0, 0], ![91, 1, 0], ![61, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-6, 1, 0], ![0, -6, 1], ![86, -49, -5]]]
  hmulB := by decide  
  f := ![![![499, -83, 0], ![8051, 0, 0]], ![![469, -78, 0], ![7567, 0, 0]], ![![319, -53, 0], ![5147, 1, 0]]]
  g := ![![![1, 0, 0], ![-91, 97, 0], ![-61, 0, 97]], ![![-1, 1, 0], ![5, -6, 1], ![50, -49, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-46, 1, 0]] ![![97, 0, 0], ![-46, 1, 0]]
  ![![97, 0, 0], ![79, 5, 1]] where
 M := ![![![9409, 0, 0], ![-4462, 97, 0]], ![![-4462, 97, 0], ![2116, -92, 1]]]
 hmul := by decide  
 g := ![![![![18, -5, -1], ![97, 0, 0]], ![![-46, 1, 0], ![0, 0, 0]]], ![![![-46, 1, 0], ![0, 0, 0]], ![![-58, -6, -1], ![98, 0, 0]]]]
 hle2 := by decide  
def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![79, 5, 1]] ![![97, 0, 0], ![-6, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-582, 97, 0]], ![![7663, 485, 97], ![-388, 0, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-6, 1, 0]]], ![![![79, 5, 1]], ![![-4, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [58, 9, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 65, 29], [52, 35, 72], [0, 1]]
 g := ![![[6, 44, 21], [72, 87], [54, 90, 77], [99, 17], [15, 49], [1]], ![[65, 19, 45, 11], [50, 79], [16, 60, 50, 29], [63, 24], [81, 54], [77, 25, 4, 48]], ![[14, 5, 25, 44], [74, 76], [8, 45, 63, 69], [17, 45], [38, 81], [18, 92, 99, 53]]]
 h' := ![![[56, 65, 29], [67, 73, 83], [100, 96, 84], [67, 1, 28], [70, 87, 44], [43, 92, 7], [0, 1]], ![[52, 35, 72], [12, 11, 73], [65, 52, 68], [70, 56, 100], [54, 57, 23], [56, 44, 85], [56, 65, 29]], ![[0, 1], [75, 17, 46], [78, 54, 50], [30, 44, 74], [39, 58, 34], [83, 66, 9], [52, 35, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 43], []]
 b := ![[], [62, 47, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [58, 9, 94, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![119180, -2222, 2222]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1180, -22, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-19, 27, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-19, 27, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![84, 27, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-19, 27, 1], ![86, -68, 28], ![2408, -1286, -40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-84, -27, 103]], ![![-1, 0, 1], ![-22, -8, 28], ![56, -2, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [85, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 102], [0, 1]]
 g := ![![[31, 17], [50, 14], [35, 15], [49], [66], [43, 1]], ![[41, 86], [34, 89], [62, 88], [49], [66], [86, 102]]]
 h' := ![![[43, 102], [76, 74], [12, 80], [46, 18], [83, 96], [53, 13], [0, 1]], ![[0, 1], [65, 29], [53, 23], [99, 85], [91, 7], [97, 90], [43, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [36, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [85, 60, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![404, 689, -623]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![512, 170, -623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-28, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-28, 1, 0]] 
 ![![103, 0, 0], ![75, 1, 0], ![40, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-28, 1, 0], ![0, -28, 1], ![86, -49, -27]]]
  hmulB := by decide  
  f := ![![![2745, -98, 0], ![10094, 0, 0]], ![![1989, -71, 0], ![7314, 0, 0]], ![![1072, -38, 0], ![3942, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 103, 0], ![-40, 0, 103]], ![![-1, 1, 0], ![20, -28, 1], ![47, -49, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-19, 27, 1]] ![![103, 0, 0], ![-28, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-2884, 103, 0]], ![![-1957, 2781, 103], ![618, -824, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-28, 1, 0]]], ![![![-19, 27, 1]], ![![6, -8, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![66, 23, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![66, 23, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![66, 23, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![66, 23, 1], ![86, 17, 24], ![2064, -1090, 41]]]
  hmulB := by decide  
  f := ![![![-65, -23, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -23, 107]], ![![0, 0, 1], ![-14, -5, 24], ![-6, -19, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [15, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 106], [0, 1]]
 g := ![![[82, 105], [9, 19], [76], [35, 1], [37], [54, 1]], ![[81, 2], [72, 88], [76], [89, 106], [37], [1, 106]]]
 h' := ![![[54, 106], [79, 31], [30, 74], [10, 66], [63, 106], [46, 12], [0, 1]], ![[0, 1], [41, 76], [67, 33], [43, 41], [9, 1], [52, 95], [54, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [47, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [15, 53, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![273, -114, -98]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![63, 20, -98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-24, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-24, 1, 0]] 
 ![![107, 0, 0], ![83, 1, 0], ![66, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-24, 1, 0], ![0, -24, 1], ![86, -49, -23]]]
  hmulB := by decide  
  f := ![![![1681, -70, 0], ![7490, 0, 0]], ![![1321, -55, 0], ![5886, 0, 0]], ![![1062, -44, 0], ![4732, 1, 0]]]
  g := ![![![1, 0, 0], ![-83, 107, 0], ![-66, 0, 107]], ![![-1, 1, 0], ![18, -24, 1], ![53, -49, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![66, 23, 1]] ![![107, 0, 0], ![-24, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-2568, 107, 0]], ![![7062, 2461, 107], ![-1498, -535, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-24, 1, 0]]], ![![![66, 23, 1]], ![![-14, -5, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-43, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-43, 1, 0]] 
 ![![109, 0, 0], ![66, 1, 0], ![4, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-43, 1, 0], ![0, -43, 1], ![86, -49, -42]]]
  hmulB := by decide  
  f := ![![![3828, -89, 0], ![9701, 0, 0]], ![![2366, -55, 0], ![5996, 0, 0]], ![![146, -3, 0], ![370, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 109, 0], ![-4, 0, 109]], ![![-1, 1, 0], ![26, -43, 1], ![32, -49, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-39, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-39, 1, 0]] 
 ![![109, 0, 0], ![70, 1, 0], ![5, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-39, 1, 0], ![0, -39, 1], ![86, -49, -38]]]
  hmulB := by decide  
  f := ![![![859, -22, 0], ![2398, 0, 0]], ![![586, -15, 0], ![1636, 0, 0]], ![![53, -1, 0], ![148, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 109, 0], ![-5, 0, 109]], ![![-1, 1, 0], ![25, -39, 1], ![34, -49, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-28, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-28, 1, 0]] 
 ![![109, 0, 0], ![81, 1, 0], ![88, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-28, 1, 0], ![0, -28, 1], ![86, -49, -27]]]
  hmulB := by decide  
  f := ![![![2409, -86, 0], ![9374, 0, 0]], ![![1821, -65, 0], ![7086, 0, 0]], ![![1968, -70, 0], ![7658, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 109, 0], ![-88, 0, 109]], ![![-1, 1, 0], ![20, -28, 1], ![59, -49, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-43, 1, 0]] ![![109, 0, 0], ![-39, 1, 0]]
  ![![109, 0, 0], ![42, 27, 1]] where
 M := ![![![11881, 0, 0], ![-4251, 109, 0]], ![![-4687, 109, 0], ![1677, -82, 1]]]
 hmul := by decide  
 g := ![![![![67, -27, -1], ![109, 0, 0]], ![![-39, 1, 0], ![0, 0, 0]]], ![![![-43, 1, 0], ![0, 0, 0]], ![![-27, -28, -1], ![110, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![42, 27, 1]] ![![109, 0, 0], ![-28, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3052, 109, 0]], ![![4578, 2943, 109], ![-1090, -763, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-28, 1, 0]]], ![![![42, 27, 1]], ![![-10, -7, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-4, 34, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-4, 34, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![109, 34, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-4, 34, 1], ![86, -53, 35], ![3010, -1629, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -34, 113]], ![![-1, 0, 1], ![-33, -11, 35], ![44, -9, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [93, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 112], [0, 1]]
 g := ![![[26, 69], [49], [100], [83], [67, 8], [68, 1]], ![[85, 44], [49], [100], [83], [46, 105], [23, 112]]]
 h' := ![![[68, 112], [44, 42], [104, 7], [108, 103], [97, 99], [4, 11], [0, 1]], ![[0, 1], [75, 71], [15, 106], [106, 10], [49, 14], [74, 102], [68, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [106, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [93, 45, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3493, -932, 398]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-353, -128, 398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-35, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-35, 1, 0]] 
 ![![113, 0, 0], ![78, 1, 0], ![18, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-35, 1, 0], ![0, -35, 1], ![86, -49, -34]]]
  hmulB := by decide  
  f := ![![![2031, -58, 0], ![6554, 0, 0]], ![![1436, -41, 0], ![4634, 0, 0]], ![![326, -9, 0], ![1052, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 113, 0], ![-18, 0, 113]], ![![-1, 1, 0], ![24, -35, 1], ![40, -49, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-4, 34, 1]] ![![113, 0, 0], ![-35, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-3955, 113, 0]], ![![-452, 3842, 113], ![226, -1243, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-35, 1, 0]]], ![![![-4, 34, 1]], ![![2, -11, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [87, 52, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 116, 119], [84, 10, 8], [0, 1]]
 g := ![![[67, 39, 87], [77, 21, 35], [123, 16, 44], [123, 101, 124], [106, 123, 11], [1]], ![[2, 73, 118, 3], [34, 75, 69, 56], [61, 43, 88, 83], [14, 41, 2, 40], [83, 61, 3, 48], [81, 124, 40, 123]], ![[84, 18, 56, 17], [103, 20, 48, 18], [114, 93, 72, 37], [7, 17, 94, 22], [122, 104, 97, 113], [121, 7, 22, 4]]]
 h' := ![![[13, 116, 119], [32, 84, 77], [94, 32, 110], [94, 45, 60], [49, 119, 39], [40, 75, 97], [0, 1]], ![[84, 10, 8], [112, 65, 98], [44, 63, 82], [90, 20, 113], [13, 10, 73], [103, 124, 116], [13, 116, 119]], ![[0, 1], [50, 105, 79], [3, 32, 62], [26, 62, 81], [0, 125, 15], [9, 55, 41], [84, 10, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 104], []]
 b := ![[], [83, 27, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [87, 52, 30, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47752, 32131, -2413]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-376, 253, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -4, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![7, -4, 0]] 
 ![![131, 0, 0], ![31, 1, 0], ![87, 0, 1]] where
  M :=![![![7, -4, 0], ![0, 7, -4], ![-344, 196, 3]]]
  hmulB := by decide  
  f := ![![![805, 12, 16]], ![![201, 3, 4]], ![![553, 8, 11]]]
  g := ![![![1, -4, 0], ![1, 7, -4], ![-51, 196, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-17, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-17, 1, 0]] 
 ![![131, 0, 0], ![114, 1, 0], ![104, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-17, 1, 0], ![0, -17, 1], ![86, -49, -16]]]
  hmulB := by decide  
  f := ![![![1089, -64, 0], ![8384, 0, 0]], ![![936, -55, 0], ![7206, 0, 0]], ![![870, -51, 0], ![6698, 1, 0]]]
  g := ![![![1, 0, 0], ![-114, 131, 0], ![-104, 0, 131]], ![![-1, 1, 0], ![14, -17, 1], ![56, -49, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-15, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-15, 1, 0]] 
 ![![131, 0, 0], ![116, 1, 0], ![37, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-15, 1, 0], ![0, -15, 1], ![86, -49, -14]]]
  hmulB := by decide  
  f := ![![![616, -41, 0], ![5371, 0, 0]], ![![556, -37, 0], ![4848, 0, 0]], ![![182, -12, 0], ![1587, 1, 0]]]
  g := ![![![1, 0, 0], ![-116, 131, 0], ![-37, 0, 131]], ![![-1, 1, 0], ![13, -15, 1], ![48, -49, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![7, -4, 0]] ![![131, 0, 0], ![-17, 1, 0]]
  ![![131, 0, 0], ![-3, 14, 1]] where
 M := ![![![917, -524, 0], ![-119, 75, -4]]]
 hmul := by decide  
 g := ![![![![7, -4, 0], ![0, 0, 0]], ![![2, -13, -1], ![127, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-3, 14, 1]] ![![131, 0, 0], ![-15, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-1965, 131, 0]], ![![-393, 1834, 131], ![131, -262, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-15, 1, 0]]], ![![![-3, 14, 1]], ![![1, -2, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![137, 0, 0], ![1, 1, 0], ![136, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![86, -49, 2]]]
  hmulB := by decide  
  f := ![![![51, -2, 1]], ![![1, 0, 0]], ![![50, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![-1, -49, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![18, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![18, 1, 0]] 
 ![![137, 0, 0], ![18, 1, 0], ![87, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![18, 1, 0], ![0, 18, 1], ![86, -49, 19]]]
  hmulB := by decide  
  f := ![![![1423, 79, 0], ![-10823, 0, 0]], ![![162, 9, 0], ![-1232, 0, 0]], ![![921, 51, 0], ![-7005, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 137, 0], ![-87, 0, 137]], ![![0, 1, 0], ![-3, 18, 1], ![-5, -49, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-20, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-20, 1, 0]] 
 ![![137, 0, 0], ![117, 1, 0], ![11, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-20, 1, 0], ![0, -20, 1], ![86, -49, -19]]]
  hmulB := by decide  
  f := ![![![1161, -58, 0], ![7946, 0, 0]], ![![981, -49, 0], ![6714, 0, 0]], ![![123, -6, 0], ![842, 1, 0]]]
  g := ![![![1, 0, 0], ![-117, 137, 0], ![-11, 0, 137]], ![![-1, 1, 0], ![17, -20, 1], ![44, -49, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![137, 0, 0], ![18, 1, 0]]
  ![![137, 0, 0], ![18, 19, 1]] where
 M := ![![![137, 137, 0], ![18, 19, 1]]]
 hmul := by decide  
 g := ![![![![-17, -18, -1], ![137, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![18, 19, 1]] ![![137, 0, 0], ![-20, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-2740, 137, 0]], ![![2466, 2603, 137], ![-274, -411, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-20, 1, 0]]], ![![![18, 19, 1]], ![![-2, -3, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB218I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB218I2 : PrimesBelowBoundCertificateInterval O 79 137 218 where
  m := 11
  g := ![1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB218I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![704969]
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![131, 131, 131]
    · exact ![137, 137, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I97N0, I97N1, I103N1, I107N1, I109N0, I109N1, I109N2, I113N1, I131N0, I131N1, I131N2, I137N0, I137N1, I137N2]
  Il := ![[], [], [I97N0, I97N0, I97N1], [], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [I113N1], [], [I131N0, I131N1, I131N2], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
