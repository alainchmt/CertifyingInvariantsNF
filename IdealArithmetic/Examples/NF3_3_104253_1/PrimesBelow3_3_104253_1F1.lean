
import IdealArithmetic.Examples.NF3_3_104253_1.RI3_3_104253_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![219457, 71879, -31399]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![219457, 71879, -31399]] 
 ![![37, 0, 0], ![0, 37, 0], ![6, 15, 1]] where
  M :=![![![219457, 71879, -31399], ![-1507152, -493639, 215637], ![3952576, 1294591, -565518]]]
  hmulB := by decide  
  f := ![![![-555, -149, -26]], ![![-1248, -1354, -447]], ![![-778, -685, -218]]]
  g := ![![![11023, 14672, -31399], ![-75702, -100762, 215637], ![198532, 264253, -565518]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [18, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 36], [0, 1]]
 g := ![![[23, 30], [9], [3, 30], [12], [1]], ![[35, 7], [9], [15, 7], [12], [1]]]
 h' := ![![[30, 36], [16, 20], [20, 3], [34, 20], [19, 30], [0, 1]], ![[0, 1], [24, 17], [36, 34], [5, 17], [31, 7], [30, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [18, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [18, 7, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![578, 890, 602]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82, -220, 602]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-555, -149, -26]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-555, -149, -26]] 
 ![![37, 0, 0], ![29, 1, 0], ![6, 0, 1]] where
  M :=![![![-555, -149, -26], ![-1248, -1354, -447], ![-6736, -4141, -1205]]]
  hmulB := by decide  
  f := ![![![219457, 71879, -31399]], ![![131273, 42996, -18782]], ![![142414, 46645, -20376]]]
  g := ![![![106, -149, -26], ![1100, -1354, -447], ![3259, -4141, -1205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![219457, 71879, -31399]] ![![-555, -149, -26]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [24, 14, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 11, 39], [11, 29, 2], [0, 1]]
 g := ![![[26, 22, 32], [29, 25], [31, 18], [31, 2, 1], []], ![[35, 23, 16, 39], [3, 37], [17, 2], [29, 22, 18, 40], [5, 4]], ![[39, 16, 40, 10], [32, 37], [14, 8], [2, 16, 1, 37], [1, 4]]]
 h' := ![![[32, 11, 39], [40, 22, 27], [30, 39, 36], [35, 10, 10], [0, 0, 1], [0, 1]], ![[11, 29, 2], [19, 8, 1], [38, 35, 23], [6, 37, 24], [2, 5, 29], [32, 11, 39]], ![[0, 1], [31, 11, 13], [15, 8, 23], [8, 35, 7], [15, 36, 11], [11, 29, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 6], []]
 b := ![[], [10, 22, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [24, 14, 39, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![139072, 171421, 103156]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3392, 4181, 2516]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [16, 22, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 18, 25], [10, 24, 18], [0, 1]]
 g := ![![[5, 16, 16], [18, 2, 17], [18, 11], [19, 16, 1], []], ![[19, 29, 38, 4], [7, 11], [22, 23], [2, 17, 16, 38], [21, 23]], ![[24, 27, 16, 20], [31, 22, 5, 5], [3, 9], [15, 8, 31, 27], [28, 23]]]
 h' := ![![[6, 18, 25], [13, 13, 4], [22, 32, 24], [40, 14, 22], [0, 0, 1], [0, 1]], ![[10, 24, 18], [9, 14, 34], [23, 30], [17, 31, 18], [1, 31, 24], [6, 18, 25]], ![[0, 1], [41, 16, 5], [31, 24, 19], [6, 41, 3], [39, 12, 18], [10, 24, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 21], []]
 b := ![[], [34, 42, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [16, 22, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-150672, -3440, -13588]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3504, -80, -316]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [23, 25, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 46, 3], [30, 0, 44], [0, 1]]
 g := ![![[41, 38, 6], [42, 5, 1], [1, 1, 24], [46, 27, 1], []], ![[21, 15, 1, 2], [20, 30, 32, 24], [36, 2, 44, 12], [15, 16], [2, 9]], ![[14, 1, 45, 15], [21, 3, 41, 30], [46, 30, 28, 5], [14, 43, 15, 44], [8, 9]]]
 h' := ![![[44, 46, 3], [21, 22, 10], [24, 11, 46], [23, 15, 27], [0, 0, 1], [0, 1]], ![[30, 0, 44], [8, 6, 19], [28, 5, 33], [13, 23, 45], [10, 31], [44, 46, 3]], ![[0, 1], [39, 19, 18], [14, 31, 15], [18, 9, 22], [11, 16, 46], [30, 0, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 30], []]
 b := ![[], [27, 36, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [23, 25, 20, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-467227, -430802, -201348]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9941, -9166, -4284]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, -89, -28]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-107, -89, -28]] 
 ![![53, 0, 0], ![0, 53, 0], ![36, 24, 1]] where
  M :=![![![-107, -89, -28], ![-1344, -896, -267], ![-3824, -2673, -807]]]
  hmulB := by decide  
  f := ![![![177, 57, -25]], ![![-1200, -391, 171]], ![![-364, -119, 52]]]
  g := ![![![17, 11, -28], ![156, 104, -267], ![476, 315, -807]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [9, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 52], [0, 1]]
 g := ![![[37, 6], [37], [25, 11], [16], [38, 1]], ![[0, 47], [37], [19, 42], [16], [23, 52]]]
 h' := ![![[38, 52], [48, 35], [40, 14], [8, 45], [29, 4], [0, 1]], ![[0, 1], [0, 18], [42, 39], [22, 8], [22, 49], [38, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [26, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [9, 15, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![569, 874, 562]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-371, -238, 562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177, -57, 25]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-177, -57, 25]] 
 ![![53, 0, 0], ![34, 1, 0], ![45, 0, 1]] where
  M :=![![![-177, -57, 25], ![1200, 391, -171], ![-3136, -1025, 448]]]
  hmulB := by decide  
  f := ![![![107, 89, 28]], ![![94, 74, 23]], ![![163, 126, 39]]]
  g := ![![![12, -57, 25], ![-83, 391, -171], ![218, -1025, 448]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-107, -89, -28]] ![![-177, -57, 25]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2537, -831, 363]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-2537, -831, 363]] 
 ![![59, 0, 0], ![17, 1, 0], ![16, 0, 1]] where
  M :=![![![-2537, -831, 363], ![17424, 5707, -2493], ![-45696, -14967, 6538]]]
  hmulB := by decide  
  f := ![![![365, -57, -42]], ![![71, -29, -15]], ![![64, -51, -23]]]
  g := ![![![98, -831, 363], ![-673, 5707, -2493], ![1765, -14967, 6538]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45095, -14770, 6452]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-45095, -14770, 6452]] 
 ![![59, 0, 0], ![24, 1, 0], ![36, 0, 1]] where
  M :=![![![-45095, -14770, 6452], ![309696, 101435, -44310], ![-812192, -266018, 116205]]]
  hmulB := by decide  
  f := ![![![-3405, -286, 80]], ![![-1320, -145, 18]], ![![-2332, -274, 25]]]
  g := ![![![1307, -14770, 6452], ![-8976, 101435, -44310], ![23540, -266018, 116205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-2537, -831, 363]] ![![-2537, -831, 363]]
  ![![-24630623, -8067291, 3524046]] where
 M := ![![![-24630623, -8067291, 3524046]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI59N1 : IdealMulLeCertificate' Table 
  ![![-24630623, -8067291, 3524046]] ![![-45095, -14770, 6452]]
  ![![59, 0, 0]] where
 M := ![![![-4249891778183, -1391971029703, 608056650044]]]
 hmul := by decide  
 g := ![![![![-72032064037, -23592729317, 10306044916]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [52, 44, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 23, 55], [3, 37, 6], [0, 1]]
 g := ![![[47, 28, 34], [22, 60], [6, 44, 49], [18, 26, 1], [1]], ![[26, 13, 11, 35], [54, 4], [42, 21, 40, 10], [27, 3, 47, 35], [60, 22, 16, 28]], ![[42, 25, 45, 40], [11, 47], [20, 35, 22, 26], [19, 20, 18, 53], [42, 31, 59, 33]]]
 h' := ![![[57, 23, 55], [3, 29, 20], [54, 24, 50], [40, 11, 7], [9, 17, 60], [0, 1]], ![[3, 37, 6], [45, 50, 17], [48, 16, 59], [33, 34, 10], [49, 4, 44], [57, 23, 55]], ![[0, 1], [22, 43, 24], [17, 21, 13], [37, 16, 44], [39, 40, 18], [3, 37, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 42], []]
 b := ![[], [6, 13, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [52, 44, 1, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![147754322, 122648064, 50703078]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2422202, 2010624, 831198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [8, 32, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 49, 62], [9, 17, 5], [0, 1]]
 g := ![![[16, 21, 17], [5, 54, 36], [38, 23], [58, 64], [15, 1], []], ![[9, 5, 40, 21], [1, 37, 9, 22], [49, 26], [50, 6], [4, 21], [19, 25]], ![[51, 13, 37, 27], [20, 66, 63, 3], [46, 21], [51, 56], [22, 56], [9, 25]]]
 h' := ![![[6, 49, 62], [27, 34, 34], [31, 7, 61], [0, 48, 31], [14, 48, 59], [0, 0, 1], [0, 1]], ![[9, 17, 5], [39, 15, 6], [32, 55, 64], [42, 21, 19], [24, 25, 26], [18, 48, 17], [6, 49, 62]], ![[0, 1], [36, 18, 27], [40, 5, 9], [41, 65, 17], [39, 61, 49], [9, 19, 49], [9, 17, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 15], []]
 b := ![[], [10, 51, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [8, 32, 52, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![97083, 80400, 33165]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1449, 1200, 495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![71, 0, 0], ![1, 1, 0], ![23, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 2, 3], ![48, 25, 1]]]
  hmulB := by decide  
  f := ![![![-73, -1, 3]], ![![1, 0, 0]], ![![-25, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 3], ![0, 25, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1957, -641, 280]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-1957, -641, 280]] 
 ![![71, 0, 0], ![27, 1, 0], ![32, 0, 1]] where
  M :=![![![-1957, -641, 280], ![13440, 4402, -1923], ![-35248, -11545, 5043]]]
  hmulB := by decide  
  f := ![![![1749, 37, -83]], ![![609, 10, -30]], ![![832, 11, -42]]]
  g := ![![![90, -641, 280], ![-618, 4402, -1923], ![1621, -11545, 5043]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-927, -649, -196]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![-927, -649, -196]] 
 ![![71, 0, 0], ![42, 1, 0], ![37, 0, 1]] where
  M :=![![![-927, -649, -196], ![-9408, -6476, -1947], ![-28016, -19361, -5827]]]
  hmulB := by decide  
  f := ![![![-39785, -13033, 5693]], ![![-19686, -6449, 2817]], ![![-30827, -10098, 4411]]]
  g := ![![![473, -649, -196], ![4713, -6476, -1947], ![14095, -19361, -5827]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![-1957, -641, 280]]
  ![![11483, 3761, -1643]] where
 M := ![![![11483, 3761, -1643]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![11483, 3761, -1643]] ![![-927, -649, -196]]
  ![![71, 0, 0]] where
 M := ![![![2059, 1420, 426]]]
 hmul := by decide  
 g := ![![![![29, 20, 6]]]]
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


lemma PB72I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 71 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 71 (by omega)

def PB72I1 : PrimesBelowBoundCertificateInterval O 31 71 72 where
  m := 9
  g := ![2, 1, 1, 1, 2, 3, 1, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71]
  hP := PB72I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0]
    · exact ![I71N0, I71N1, I71N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![79507]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![300763]
    · exact ![71, 71, 71]
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
  β := ![I37N1, I53N1, I59N0, I59N1, I71N0, I71N1, I71N2]
  Il := ![[I37N1], [], [], [], [I53N1], [I59N0, I59N0, I59N1], [], [], [I71N0, I71N1, I71N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
