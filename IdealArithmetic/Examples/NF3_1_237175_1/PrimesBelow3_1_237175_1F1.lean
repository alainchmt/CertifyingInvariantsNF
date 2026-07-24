
import IdealArithmetic.Examples.NF3_1_237175_1.RI3_1_237175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5865291, 4364626, -490724]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![5865291, 4364626, -490724]] 
 ![![37, 0, 0], ![0, 37, 0], ![2, 31, 1]] where
  M :=![![![5865291, 4364626, -490724], ![24432420, 13278041, 16477056], ![-122001968, -94936544, 25881195]]]
  hmulB := by decide  
  f := ![![![51565576223607, -1793894486222, 2119784876020]], ![![-71420905005084, 2484633685349, -2936008192848]], ![![-57562825261838, 2002530416819, -2366322949285]]]
  g := ![![![185047, 529110, -490724], ![-230316, -13446235, 16477056], ![-4696334, -24250097, 25881195]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 36], [0, 1]]
 g := ![![[10, 1], [34], [28, 28], [26], [1]], ![[0, 36], [34], [7, 9], [26], [1]]]
 h' := ![![[27, 36], [10, 1], [9, 21], [12, 19], [36, 27], [0, 1]], ![[0, 1], [0, 36], [21, 16], [7, 18], [25, 10], [27, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [13, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-930, -429, -872]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, 719, -872]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51565576223607, 1793894486222, -2119784876020]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-51565576223607, 1793894486222, -2119784876020]] 
 ![![37, 0, 0], ![22, 1, 0], ![33, 0, 1]] where
  M :=![![![-51565576223607, 1793894486222, -2119784876020], ![71420905005084, -2484633685349, 2936008192848], ![18907631977616, -657770148928, 777264897297]]]
  hmulB := by decide  
  f := ![![![-5865291, -4364626, 490724]], ![![-4147806, -2954049, -153544]], ![![-1933855, -1326922, -261819]]]
  g := ![![![-569685243563, 1793894486222, -2119784876020], ![789042586994, -2484633685349, 2936008192848], ![208887395763, -657770148928, 777264897297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![5865291, 4364626, -490724]] ![![-51565576223607, 1793894486222, -2119784876020]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [29, 11, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 16, 13], [2, 24, 28], [0, 1]]
 g := ![![[31, 13, 37], [36, 5], [4, 32], [14, 5, 1], []], ![[39, 24, 34, 29], [26, 18], [], [2, 40, 14, 26], [31, 5]], ![[29, 4, 18, 17], [15, 37], [18, 32], [9, 35, 38, 34], [16, 5]]]
 h' := ![![[3, 16, 13], [18, 23, 23], [23, 39, 28], [4, 29, 27], [0, 0, 1], [0, 1]], ![[2, 24, 28], [35, 8, 31], [25, 36, 31], [5, 20], [12, 20, 24], [3, 16, 13]], ![[0, 1], [21, 10, 28], [13, 7, 23], [24, 33, 14], [32, 21, 16], [2, 24, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 22], []]
 b := ![[], [3, 25, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [29, 11, 36, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![161253, 78064, 142352]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3933, 1904, 3472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [9, 12, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 0, 8], [6, 42, 35], [0, 1]]
 g := ![![[12, 36, 24], [42, 28, 9], [17, 13], [29, 27, 1], []], ![[38, 34, 12, 18], [21, 40, 27, 29], [23, 23], [11, 20, 3, 8], [8, 21]], ![[10, 7, 26, 40], [12, 15], [13, 4], [20, 16], [24, 21]]]
 h' := ![![[21, 0, 8], [9, 28, 29], [28, 0, 3], [40, 11, 20], [0, 0, 1], [0, 1]], ![[6, 42, 35], [32, 34, 23], [17, 5, 40], [40, 19, 25], [25, 16, 42], [21, 0, 8]], ![[0, 1], [31, 24, 34], [4, 38], [32, 13, 41], [35, 27], [6, 42, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 17], []]
 b := ![[], [13, 42, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [9, 12, 16, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-385820940, -248192603, -114583906]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8972580, -5771921, -2664742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![19, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![19, 1, 0]] 
 ![![47, 0, 0], ![19, 1, 0], ![9, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![19, 1, 0], ![2, 18, 4], ![-32, -24, 21]]]
  hmulB := by decide  
  f := ![![![42, 539, 120], ![47, -1410, 0]], ![![5, 215, 48], ![48, -564, 0]], ![![4, 103, 23], ![19, -270, 0]]]
  g := ![![![1, 0, 0], ![-19, 47, 0], ![-9, 0, 47]], ![![0, 1, 0], ![-8, 18, 4], ![5, -24, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-12, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-12, 1, 0]] 
 ![![47, 0, 0], ![35, 1, 0], ![32, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-12, 1, 0], ![2, -13, 4], ![-32, -24, -10]]]
  hmulB := by decide  
  f := ![![![2193, -15634, 4816], ![-846, -56588, 0]], ![![1625, -11634, 3584], ![-657, -42112, 0]], ![![1488, -10644, 3279], ![-596, -38528, 0]]]
  g := ![![![1, 0, 0], ![-35, 47, 0], ![-32, 0, 47]], ![![-1, 1, 0], ![7, -13, 4], ![24, -24, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28271, -18758, -6246]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-28271, -18758, -6246]] 
 ![![47, 0, 0], ![39, 1, 0], ![6, 0, 1]] where
  M :=![![![-28271, -18758, -6246], ![162356, 140391, -87524], ![825112, 575112, 77871]]]
  hmulB := by decide  
  f := ![![![-61268490249, 2131445334, -2518657378]], ![![-49034280701, 1705834245, -2015727046]], ![![-7343521842, 255470884, -301881365]]]
  g := ![![![15761, -18758, -6246], ![-101867, 140391, -87524], ![-469606, 575112, 77871]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![19, 1, 0]] ![![47, 0, 0], ![-12, 1, 0]]
  ![![-61268490249, 2131445334, -2518657378]] where
 M := ![![![2209, 0, 0], ![-564, 47, 0]], ![![893, 47, 0], ![-226, 6, 4]]]
 hmul := by decide  
 g := ![![![![-1328737, -881626, -293562]], ![![501608, 365487, -12572]]], ![![![-374793, -216011, -206198]], ![![226890, 157066, 25488]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-61268490249, 2131445334, -2518657378]] ![![-28271, -18758, -6246]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![11, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![11, 1, 0]] 
 ![![53, 0, 0], ![11, 1, 0], ![26, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![11, 1, 0], ![2, 10, 4], ![-32, -24, 13]]]
  hmulB := by decide  
  f := ![![![-1151, -6084, -2436], ![-318, 32277, 0]], ![![-241, -1259, -504], ![-52, 6678, 0]], ![![-569, -2985, -1195], ![-135, 15834, 0]]]
  g := ![![![1, 0, 0], ![-11, 53, 0], ![-26, 0, 53]], ![![0, 1, 0], ![-4, 10, 4], ![-2, -24, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2430321, 1543472, 797812]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![2430321, 1543472, 797812]] 
 ![![53, 0, 0], ![30, 1, 0], ![48, 0, 1]] where
  M :=![![![2430321, 1543472, 797812], ![-22443040, -18260639, 7769512], ![-78112336, -52999568, -12832411]]]
  hmulB := by decide  
  f := ![![![646108804341445, -22477224274224, 26560581147532]], ![![348837190282526, -12135559380223, 14340183011776]], ![![580685148374592, -20201226519472, 23871111027949]]]
  g := ![![![-1550355, 1543472, 797812], ![2876218, -18260639, 7769512], ![40147744, -52999568, -12832411]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![11, 1, 0]] ![![53, 0, 0], ![11, 1, 0]]
  ![![-646108804341445, 22477224274224, -26560581147532]] where
 M := ![![![2809, 0, 0], ![583, 53, 0]], ![![583, 53, 0], ![123, 21, 4]]]
 hmul := by decide  
 g := ![![![![-128807013, -81804016, -42284036]], ![![-4290491, 1282447, -16545444]]], ![![![-4290491, 1282447, -16545444]], ![![9147617, 7653295, -3961528]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-646108804341445, 22477224274224, -26560581147532]] ![![2430321, 1543472, 797812]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![8, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![8, 1, 0]] 
 ![![59, 0, 0], ![8, 1, 0], ![16, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![8, 1, 0], ![2, 7, 4], ![-32, -24, 10]]]
  hmulB := by decide  
  f := ![![![1581, 5692, 3256], ![354, -48026, 0]], ![![212, 769, 440], ![60, -6490, 0]], ![![424, 1543, 883], ![131, -13024, 0]]]
  g := ![![![1, 0, 0], ![-8, 59, 0], ![-16, 0, 59]], ![![0, 1, 0], ![-2, 7, 4], ![0, -24, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![10, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![10, 1, 0]] 
 ![![59, 0, 0], ![10, 1, 0], ![37, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![10, 1, 0], ![2, 9, 4], ![-32, -24, 12]]]
  hmulB := by decide  
  f := ![![![-239, -1080, -480], ![0, 7080, 0]], ![![-40, -180, -80], ![1, 1180, 0]], ![![-147, -677, -301], ![-17, 4440, 0]]]
  g := ![![![1, 0, 0], ![-10, 59, 0], ![-37, 0, 59]], ![![0, 1, 0], ![-4, 9, 4], ![-4, -24, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-19, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-19, 1, 0]] 
 ![![59, 0, 0], ![40, 1, 0], ![53, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-19, 1, 0], ![2, -20, 4], ![-32, -24, -17]]]
  hmulB := by decide  
  f := ![![![2182, -25401, 5084], ![-1121, -74989, 0]], ![![1476, -17207, 3444], ![-766, -50799, 0]], ![![1963, -22818, 4567], ![-998, -67363, 0]]]
  g := ![![![1, 0, 0], ![-40, 59, 0], ![-53, 0, 59]], ![![-1, 1, 0], ![10, -20, 4], ![31, -24, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![8, 1, 0]] ![![59, 0, 0], ![10, 1, 0]]
  ![![59, 0, 0], ![-9, 19, 1]] where
 M := ![![![3481, 0, 0], ![590, 59, 0]], ![![472, 59, 0], ![82, 17, 4]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![10, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![2, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-9, 19, 1]] ![![59, 0, 0], ![-19, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1121, 59, 0]], ![![-531, 1121, 59], ![177, -413, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-19, 1, 0]]], ![![![-9, 19, 1]], ![![3, -7, 1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![46, 2, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![46, 2, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![46, 2, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![46, 2, 1], ![-28, 20, 10], ![-100, -68, 27]]]
  hmulB := by decide  
  f := ![![![-45, -2, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -2, 61]], ![![0, 0, 1], ![-8, 0, 10], ![-22, -2, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [11, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 60], [0, 1]]
 g := ![![[48, 58], [34], [20, 16], [23, 9], [21, 1]], ![[46, 3], [34], [51, 45], [29, 52], [42, 60]]]
 h' := ![![[21, 60], [19, 27], [24, 20], [52, 4], [13, 3], [0, 1]], ![[0, 1], [37, 34], [17, 41], [14, 57], [15, 58], [21, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [42, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [11, 40, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1303, -237, -2223]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1655, 69, -2223]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-10, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-10, 1, 0]] 
 ![![61, 0, 0], ![51, 1, 0], ![34, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-10, 1, 0], ![2, -11, 4], ![-32, -24, -8]]]
  hmulB := by decide  
  f := ![![![-85, 527, -192], ![61, 2928, 0]], ![![-69, 439, -160], ![62, 2440, 0]], ![![-50, 294, -107], ![18, 1632, 0]]]
  g := ![![![1, 0, 0], ![-51, 61, 0], ![-34, 0, 61]], ![![-1, 1, 0], ![7, -11, 4], ![24, -24, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![46, 2, 1]] ![![61, 0, 0], ![-10, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-610, 61, 0]], ![![2806, 122, 61], ![-488, 0, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-10, 1, 0]]], ![![![46, 2, 1]], ![![-8, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![8, -15, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![8, -15, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![8, 52, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![8, -15, 1], ![-62, -1, -58], ![444, 340, -45]]]
  hmulB := by decide  
  f := ![![![-7, 15, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -52, 67]], ![![0, -1, 1], ![6, 45, -58], ![12, 40, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [10, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 66], [0, 1]]
 g := ![![[27, 47], [19, 25], [21], [19], [4], [1]], ![[0, 20], [36, 42], [21], [19], [4], [1]]]
 h' := ![![[65, 66], [11, 39], [40, 62], [60, 50], [60, 32], [57, 65], [0, 1]], ![[0, 1], [0, 28], [50, 5], [27, 17], [63, 35], [61, 2], [65, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [41, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [10, 2, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-897, -437, -824]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85, 633, -824]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-9, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-9, 1, 0]] 
 ![![67, 0, 0], ![58, 1, 0], ![45, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-9, 1, 0], ![2, -10, 4], ![-32, -24, -7]]]
  hmulB := by decide  
  f := ![![![5767, -29622, 11856], ![-1206, -198588, 0]], ![![4996, -25635, 10260], ![-1004, -171855, 0]], ![![3879, -19896, 7963], ![-768, -133380, 0]]]
  g := ![![![1, 0, 0], ![-58, 67, 0], ![-45, 0, 67]], ![![-1, 1, 0], ![6, -10, 4], ![25, -24, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![8, -15, 1]] ![![67, 0, 0], ![-9, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-603, 67, 0]], ![![536, -1005, 67], ![-134, 134, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-9, 1, 0]]], ![![![8, -15, 1]], ![![-2, 2, -1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![21, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![21, 1, 0]] 
 ![![71, 0, 0], ![21, 1, 0], ![2, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![21, 1, 0], ![2, 20, 4], ![-32, -24, 23]]]
  hmulB := by decide  
  f := ![![![-3652, -41337, -8272], ![-1633, 146828, 0]], ![![-1096, -12214, -2444], ![-425, 43381, 0]], ![![-115, -1165, -233], ![-5, 4136, 0]]]
  g := ![![![1, 0, 0], ![-21, 71, 0], ![-2, 0, 71]], ![![0, 1, 0], ![-6, 20, 4], ![6, -24, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-19, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-19, 1, 0]] 
 ![![71, 0, 0], ![52, 1, 0], ![12, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-19, 1, 0], ![2, -20, 4], ![-32, -24, -17]]]
  hmulB := by decide  
  f := ![![![6447, -71642, 14336], ![-2698, -254464, 0]], ![![4717, -52452, 10496], ![-1987, -186304, 0]], ![![1099, -12109, 2423], ![-421, -43008, 0]]]
  g := ![![![1, 0, 0], ![-52, 71, 0], ![-12, 0, 71]], ![![-1, 1, 0], ![14, -20, 4], ![20, -24, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-3, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-3, 1, 0]] 
 ![![71, 0, 0], ![68, 1, 0], ![33, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-3, 1, 0], ![2, -4, 4], ![-32, -24, -1]]]
  hmulB := by decide  
  f := ![![![1972, -3947, 3948], ![-71, -70077, 0]], ![![1888, -3779, 3780], ![-70, -67095, 0]], ![![918, -1835, 1835], ![1, -32571, 0]]]
  g := ![![![1, 0, 0], ![-68, 71, 0], ![-33, 0, 71]], ![![-1, 1, 0], ![2, -4, 4], ![23, -24, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![21, 1, 0]] ![![71, 0, 0], ![-19, 1, 0]]
  ![![71, 0, 0], ![25, 18, 1]] where
 M := ![![![5041, 0, 0], ![-1349, 71, 0]], ![![1491, 71, 0], ![-397, 1, 4]]]
 hmul := by decide  
 g := ![![![![46, -18, -1], ![71, 0, 0]], ![![-19, 1, 0], ![0, 0, 0]]], ![![![-4, -17, -1], ![71, 0, 0]], ![![-7, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![25, 18, 1]] ![![71, 0, 0], ![-3, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-213, 71, 0]], ![![1775, 1278, 71], ![-71, -71, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-3, 1, 0]]], ![![![25, 18, 1]], ![![-1, -1, 1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [39, 37, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 64, 56], [34, 8, 17], [0, 1]]
 g := ![![[66, 71, 65], [40, 23], [18, 50], [38, 70, 12], [15, 1], []], ![[23, 66, 59, 60], [16, 9], [24, 57], [26, 20, 13, 13], [11, 64], [42, 70]], ![[35, 15, 33, 26], [26, 37], [9, 65], [32, 0, 57, 59], [47, 8], [8, 70]]]
 h' := ![![[54, 64, 56], [47, 31, 49], [1, 36, 13], [51, 26, 14], [72, 63, 42], [0, 0, 1], [0, 1]], ![[34, 8, 17], [30, 13, 11], [17, 41, 3], [2, 58, 35], [64, 17, 68], [37, 0, 8], [54, 64, 56]], ![[0, 1], [44, 29, 13], [6, 69, 57], [49, 62, 24], [67, 66, 36], [41, 0, 64], [34, 8, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 66], []]
 b := ![[], [28, 18, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [39, 37, 58, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![104968379, 67422508, 31583304]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1437923, 923596, 432648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![4, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![4, 1, 0]] 
 ![![79, 0, 0], ![4, 1, 0], ![37, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![4, 1, 0], ![2, 3, 4], ![-32, -24, 6]]]
  hmulB := by decide  
  f := ![![![-1875, -2819, -3760], ![-79, 74260, 0]], ![![-94, -141, -188], ![1, 3713, 0]], ![![-877, -1320, -1761], ![-60, 34780, 0]]]
  g := ![![![1, 0, 0], ![-4, 79, 0], ![-37, 0, 79]], ![![0, 1, 0], ![-2, 3, 4], ![-2, -24, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![12, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![12, 1, 0]] 
 ![![79, 0, 0], ![12, 1, 0], ![7, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![12, 1, 0], ![2, 11, 4], ![-32, -24, 14]]]
  hmulB := by decide  
  f := ![![![-1469, -8345, -3036], ![-316, 59961, 0]], ![![-230, -1265, -460], ![1, 9085, 0]], ![![-137, -740, -269], ![17, 5313, 0]]]
  g := ![![![1, 0, 0], ![-12, 79, 0], ![-7, 0, 79]], ![![0, 1, 0], ![-2, 11, 4], ![2, -24, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 0, -30]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-11, 0, -30]] 
 ![![79, 0, 0], ![62, 1, 0], ![3, 0, 1]] where
  M :=![![![-11, 0, -30], ![960, 709, -60], ![1080, 600, 679]]]
  hmulB := by decide  
  f := ![![![517411, -18000, 21270]], ![![396998, -13811, 16320]], ![![17247, -600, 709]]]
  g := ![![![1, 0, -30], ![-542, 709, -60], ![-483, 600, 679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![4, 1, 0]] ![![79, 0, 0], ![12, 1, 0]]
  ![![-517411, 18000, -21270]] where
 M := ![![![6241, 0, 0], ![948, 79, 0]], ![![316, 79, 0], ![50, 15, 4]]]
 hmul := by decide  
 g := ![![![![869, 0, 2370]], ![![-828, -709, 420]]], ![![![-916, -709, 180]], ![![-230, -165, -4]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-517411, 18000, -21270]] ![![-11, 0, -30]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB138I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB138I1 : PrimesBelowBoundCertificateInterval O 31 79 138 where
  m := 11
  g := ![2, 1, 1, 3, 3, 3, 2, 2, 3, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB138I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![53, 53, 53]
    · exact ![59, 59, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![389017]
    · exact ![79, 79, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I37N1, I47N0, I47N1, I47N2, I53N0, I53N1, I59N0, I59N1, I59N2, I61N1, I67N1, I71N0, I71N1, I71N2, I79N0, I79N1, I79N2]
  Il := ![[I37N1], [], [], [I47N0, I47N1, I47N2], [I53N0, I53N0, I53N1], [I59N0, I59N1, I59N2], [I61N1], [I67N1], [I71N0, I71N1, I71N2], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
