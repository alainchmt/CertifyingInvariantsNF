
import IdealArithmetic.Examples.NF3_1_411060_1.RI3_1_411060_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [36, 13, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16, 7], [1, 20, 30], [0, 1]]
 g := ![![[7, 33, 10], [26, 36], [14, 16, 11], [8, 1], []], ![[8, 19, 19, 21], [22, 4], [35, 33, 1, 26], [12, 30], [24, 12]], ![[33, 35, 20, 4], [35, 16], [23, 24, 4, 12], [3, 34], [1, 12]]]
 h' := ![![[7, 16, 7], [0, 24, 26], [14, 9, 6], [8, 8, 14], [0, 0, 1], [0, 1]], ![[1, 20, 30], [31, 36, 22], [34, 21, 35], [13, 26, 3], [36, 35, 20], [7, 16, 7]], ![[0, 1], [2, 14, 26], [35, 7, 33], [7, 3, 20], [2, 2, 16], [1, 20, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 25], []]
 b := ![[], [11, 8, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [36, 13, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-815406, 433899, -196544]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22038, 11727, -5312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9725088530217385061, -211283780374632167, -454297347531741889]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-9725088530217385061, -211283780374632167, -454297347531741889]] 
 ![![41, 0, 0], ![0, 41, 0], ![9, 32, 1]] where
  M :=![![![-9725088530217385061, -211283780374632167, -454297347531741889], ![-51789897618618575346, -1125168713896766725, -2419310944468386502], ![-75876248581326642384, -1648460123637523662, -3544479658365153227]]]
  hmulB := by decide  
  f := ![![![-305208811, -160878649, 148927651]], ![![16977752214, -2664149231, -357610292]], ![![13150701897, -2000432579, -320120488]]]
  g := ![![![-137473473230041660, 349420276601002641, -454297347531741889], ![-732099978497636508, 1860799549002234179, -2419310944468386502], ![-1072583698927811301, 2726216803513350722, -3544479658365153227]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [18, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 40], [0, 1]]
 g := ![![[37, 16], [16], [16], [16, 18], [1]], ![[0, 25], [16], [16], [0, 23], [1]]]
 h' := ![![[31, 40], [40, 4], [0, 37], [40, 4], [23, 31], [0, 1]], ![[0, 1], [0, 37], [40, 4], [0, 37], [0, 10], [31, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [26, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [18, 10, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1035, 2204, -1279]
  a := ![-1, -4, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![306, 1052, -1279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-305208811, -160878649, 148927651]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-305208811, -160878649, 148927651]] 
 ![![41, 0, 0], ![1, 1, 0], ![33, 0, 1]] where
  M :=![![![-305208811, -160878649, 148927651], ![16977752214, -2664149231, -357610292], ![-1362413772, 4682947494, -3021759523]]]
  hmulB := by decide  
  f := ![![![-9725088530217385061, -211283780374632167, -454297347531741889]], ![![-1500365515825267327, -32596402299302412, -70088007121954351]], ![![-9678150489719520717, -210264021365863053, -452104686022259404]]]
  g := ![![![-123388845, -160878649, 148927651], ![766903441, -2664149231, -357610292], ![2284700073, 4682947494, -3021759523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-9725088530217385061, -211283780374632167, -454297347531741889]] ![![-305208811, -160878649, 148927651]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-8, 3, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-8, 3, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![35, 3, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-8, 3, 1], ![114, -32, 18], ![456, -42, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -3, 43]], ![![-1, 0, 1], ![-12, -2, 18], ![22, 0, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [28, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 42], [0, 1]]
 g := ![![[33, 14], [17, 4], [17], [42, 11], [1]], ![[40, 29], [19, 39], [17], [26, 32], [1]]]
 h' := ![![[22, 42], [40, 10], [7, 41], [28, 24], [15, 22], [0, 1]], ![[0, 1], [2, 33], [6, 2], [40, 19], [26, 21], [22, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [10, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [28, 21, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2780, 11, 147]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55, -10, 147]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-18, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-18, 1, 0]] 
 ![![43, 0, 0], ![25, 1, 0], ![14, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-18, 1, 0], ![0, -20, 5], ![114, -18, -15]]]
  hmulB := by decide  
  f := ![![![505, -28, 0], ![1204, 0, 0]], ![![307, -17, 0], ![732, 0, 0]], ![![182, 2, -3], ![434, 26, 0]]]
  g := ![![![1, 0, 0], ![-25, 43, 0], ![-14, 0, 43]], ![![-1, 1, 0], ![10, -20, 5], ![18, -18, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-8, 3, 1]] ![![43, 0, 0], ![-18, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-774, 43, 0]], ![![-344, 129, 43], ![258, -86, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-18, 1, 0]]], ![![![-8, 3, 1]], ![![6, -2, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [15, 39, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6, 30], [22, 40, 17], [0, 1]]
 g := ![![[9, 17, 34], [25], [35, 17, 28], [40, 28, 1], []], ![[27, 43, 13, 40], [10, 9, 32, 33], [31, 46, 38, 11], [16, 8, 38, 13], [39, 7]], ![[36, 15, 13, 25], [44, 30, 7, 14], [29, 30, 21, 16], [10, 14, 12, 1], [5, 7]]]
 h' := ![![[6, 6, 30], [1, 29, 9], [39, 5], [11, 41, 13], [0, 0, 1], [0, 1]], ![[22, 40, 17], [28, 6, 8], [22, 30, 9], [29, 19, 11], [15, 44, 40], [6, 6, 30]], ![[0, 1], [43, 12, 30], [8, 12, 38], [26, 34, 23], [33, 3, 6], [22, 40, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 36], []]
 b := ![[], [12, 42, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [15, 39, 19, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3278908, 1449574, -595725]
  a := ![1, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-69764, 30842, -12675]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![32, 18, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![32, 18, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![32, 18, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![32, 18, 1], ![114, -22, 93], ![2166, -312, 71]]]
  hmulB := by decide  
  f := ![![![-31, -18, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -18, 53]], ![![0, 0, 1], ![-54, -32, 93], ![-2, -30, 71]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [41, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 52], [0, 1]]
 g := ![![[11, 10], [47], [11, 13], [1], [26, 1]], ![[6, 43], [47], [31, 40], [1], [52, 52]]]
 h' := ![![[26, 52], [21, 13], [26, 43], [48, 38], [47, 52], [0, 1]], ![[0, 1], [41, 40], [31, 10], [29, 15], [21, 1], [26, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [28, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [41, 27, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1865, 1695, -1275]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![805, 465, -1275]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![13, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![13, 1, 0]] 
 ![![53, 0, 0], ![13, 1, 0], ![35, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![13, 1, 0], ![0, 11, 5], ![114, -18, 16]]]
  hmulB := by decide  
  f := ![![![482, 37, 0], ![-1961, 0, 0]], ![![104, 8, 0], ![-423, 0, 0]], ![![308, 17, -3], ![-1253, 32, 0]]]
  g := ![![![1, 0, 0], ![-13, 53, 0], ![-35, 0, 53]], ![![0, 1, 0], ![-6, 11, 5], ![-4, -18, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![32, 18, 1]] ![![53, 0, 0], ![13, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![689, 53, 0]], ![![1696, 954, 53], ![530, 212, 106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![13, 1, 0]]], ![![![32, 18, 1]], ![![10, 4, 2]]]]
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
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![64253980268094174585031644107, -19484529549946122571440045360, 5063852670586039610750768572]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![64253980268094174585031644107, -19484529549946122571440045360, 5063852670586039610750768572]] 
 ![![59, 0, 0], ![0, 59, 0], ![3, 7, 1]] where
  M :=![![![64253980268094174585031644107, -19484529549946122571440045360, 5063852670586039610750768572], ![577279204446808515625587617208, 12073691297437706734397900531, -82231089737972494024947921084], ![-1643957164247049457518577553832, 411487763946062681614930039344, -70157398440534787290550020553]]]
  hmulB := by decide  
  f := ![![![-559153024951253701565762370392889841526588607209712330767, -12147957784911920250025830209331492954245311613609261232, -26120249220397204415247427937865365539499330778088194212]], ![![-2977708411125281303338206784916651671502923708702054140168, -64692623414280181591257007092650275907110029976906312487, -139100536585751214495871434860253561389724550402310888796]], ![![-455660907649762210845862475158909713447239339240627557527, -9899525216458456277481029351914642771357330592733281347, -21285723114601381539050352030309743451583125856434881449]]]
  g := ![![![831566478920950097504734549, -931042343119464404181278396, 5063852670586039610750768572], ![13965635146791966062719175940, 9960869821410934998458192341, -82231089737972494024947921084], ![-24296355405516018570286906647, 15298128017454342248284409885, -70157398440534787290550020553]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [50, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 58], [0, 1]]
 g := ![![[7, 4], [44, 5], [41], [52, 35], [4, 1]], ![[23, 55], [5, 54], [41], [15, 24], [8, 58]]]
 h' := ![![[4, 58], [42, 2], [31, 8], [55, 49], [36, 25], [0, 1]], ![[0, 1], [50, 57], [4, 51], [15, 10], [18, 34], [4, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [50, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [50, 55, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![141466, 90921, -59733]
  a := ![1, -21, 62]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5435, 8628, -59733]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![206695793133515, -30371846851128, -5761750960448]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![206695793133515, -30371846851128, -5761750960448]] 
 ![![59, 0, 0], ![21, 1, 0], ![50, 0, 1]] where
  M :=![![![206695793133515, -30371846851128, -5761750960448], ![-656839609491072, 371151004123835, -169144487136984], ![-4119230150519664, 477552231794928, 202006516986851]]]
  hmulB := by decide  
  f := ![![![155750248947303481161603110737, 3383773966645913059955510184, 7275710113518813920369996032]], ![![69494681031093523581624489375, 1509816479156562351425387723, 3246371399282730498112838232]], ![![152588027669558524302326495686, 3315072682964321779034174208, 7127990251193215382278296651]]]
  g := ![![![19196476695417, -30371846851128, -5761750960448], ![105316284027, 371151004123835, -169144487136984], ![-410985641822978, 477552231794928, 202006516986851]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![64253980268094174585031644107, -19484529549946122571440045360, 5063852670586039610750768572]] ![![206695793133515, -30371846851128, -5761750960448]]
  ![![59, 0, 0]] where
 M := ![![![5220063595735277738163797867381478809772217, -6764960611301925387438745863739073073255480, 3948416565828397736735609790183115592361076]]]
 hmul := by decide  
 g := ![![![![88475654165004707426505048599686081521563, -114660349344100430295571963792187679207720, 66922314675057588758230674409883315124764]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [50, 11, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 41, 22], [18, 19, 39], [0, 1]]
 g := ![![[47, 15, 48], [13, 3], [17, 43, 42], [41, 4, 13], [1]], ![[4, 45, 26, 56], [34, 27], [10, 7, 42, 19], [55, 16, 43, 16], [52, 7, 8, 34]], ![[13, 27, 51, 60], [17, 12], [37, 28, 55, 19], [8, 55, 40, 5], [23, 5, 4, 27]]]
 h' := ![![[29, 41, 22], [37, 15, 29], [4, 8, 53], [24, 19, 15], [11, 50, 47], [0, 1]], ![[18, 19, 39], [27, 49, 27], [18, 34, 24], [23, 34, 32], [12, 41, 41], [29, 41, 22]], ![[0, 1], [3, 58, 5], [11, 19, 45], [51, 8, 14], [46, 31, 34], [18, 19, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 60], []]
 b := ![[], [58, 11, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [50, 11, 14, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![73810, -37698, 19398]
  a := ![-1, -1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1210, -618, 318]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-1, -10, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-1, -10, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![66, 57, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-1, -10, 1], ![114, 1, -47], ![-1026, 192, -46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -57, 67]], ![![-1, -1, 1], ![48, 40, -47], ![30, 42, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [44, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 66], [0, 1]]
 g := ![![[61, 37], [46, 56], [40], [65], [16], [1]], ![[47, 30], [23, 11], [40], [65], [16], [1]]]
 h' := ![![[63, 66], [53, 38], [41, 18], [27, 43], [26, 20], [23, 63], [0, 1]], ![[0, 1], [35, 29], [36, 49], [56, 24], [13, 47], [39, 4], [63, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [62, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [44, 4, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4490, 4298, -2748]
  a := ![0, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2774, 2402, -2748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-20, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-20, 1, 0]] 
 ![![67, 0, 0], ![47, 1, 0], ![46, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-20, 1, 0], ![0, -22, 5], ![114, -18, -17]]]
  hmulB := by decide  
  f := ![![![1261, -63, 0], ![4221, 0, 0]], ![![881, -44, 0], ![2949, 0, 0]], ![![898, -36, -2], ![3006, 27, 0]]]
  g := ![![![1, 0, 0], ![-47, 67, 0], ![-46, 0, 67]], ![![-1, 1, 0], ![12, -22, 5], ![26, -18, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-1, -10, 1]] ![![67, 0, 0], ![-20, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1340, 67, 0]], ![![-67, -670, 67], ![134, 201, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-20, 1, 0]]], ![![![-1, -10, 1]], ![![2, 3, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-322091, 58453, 1385]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-322091, 58453, 1385]] 
 ![![71, 0, 0], ![14, 1, 0], ![9, 0, 1]] where
  M :=![![![-322091, 58453, 1385], ![157890, -463927, 296420], ![6821532, -1035534, -167507]]]
  hmulB := by decide  
  f := ![![![384664008269, 8357072081, 17969177155]], ![![104701159316, 2274699781, 4891005240]], ![![91030542075, 1977696861, 4252396642]]]
  g := ![![![-16238, 58453, 1385], ![56128, -463927, 296420], ![321501, -1035534, -167507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![20, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![20, 1, 0]] 
 ![![71, 0, 0], ![20, 1, 0], ![70, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![20, 1, 0], ![0, 18, 5], ![114, -18, 23]]]
  hmulB := by decide  
  f := ![![![601, 30, 0], ![-2130, 0, 0]], ![![140, 7, 0], ![-496, 0, 0]], ![![610, 16, -4], ![-2162, 57, 0]]]
  g := ![![![1, 0, 0], ![-20, 71, 0], ![-70, 0, 71]], ![![0, 1, 0], ![-10, 18, 5], ![-16, -18, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-35, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-35, 1, 0]] 
 ![![71, 0, 0], ![36, 1, 0], ![25, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-35, 1, 0], ![0, -37, 5], ![114, -18, -32]]]
  hmulB := by decide  
  f := ![![![2486, -71, 0], ![5041, 0, 0]], ![![1296, -37, 0], ![2628, 0, 0]], ![![900, 4, -4], ![1825, 57, 0]]]
  g := ![![![1, 0, 0], ![-36, 71, 0], ![-25, 0, 71]], ![![-1, 1, 0], ![17, -37, 5], ![22, -18, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-322091, 58453, 1385]] ![![71, 0, 0], ![20, 1, 0]]
  ![![71, 0, 0], ![-15, -22, 1]] where
 M := ![![![-22868461, 4150163, 98335], ![-6283930, 705133, 324120]]]
 hmul := by decide  
 g := ![![![![-312836, 72027, 768], ![43807, 0, 0]], ![![-85595, 14201, 4371], ![13779, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-15, -22, 1]] ![![71, 0, 0], ![-35, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2485, 71, 0]], ![![-1065, -1562, 71], ![639, 781, -142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-35, 1, 0]]], ![![![-15, -22, 1]], ![![9, 11, -2]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [72, 53, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 11, 9], [57, 61, 64], [0, 1]]
 g := ![![[31, 40, 57], [3, 2], [4, 48], [53, 23, 19], [15, 1], []], ![[17, 16, 1, 37], [70, 64], [58, 67], [4, 9, 69, 55], [57, 71], [26, 8]], ![[41, 40, 49, 32], [7, 67], [69, 38], [10, 49, 62, 61], [15, 48], [44, 8]]]
 h' := ![![[31, 11, 9], [64, 4, 35], [39, 3, 32], [53, 67, 11], [15, 9, 26], [0, 0, 1], [0, 1]], ![[57, 61, 64], [58, 54, 54], [34, 63, 8], [66, 31, 33], [41, 23, 61], [38, 42, 61], [31, 11, 9]], ![[0, 1], [61, 15, 57], [28, 7, 33], [18, 48, 29], [6, 41, 59], [8, 31, 11], [57, 61, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 50], []]
 b := ![[], [7, 61, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [72, 53, 58, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9023822, 6114918, -3140460]
  a := ![2, 6, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-123614, 83766, -43020]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-15, 20, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-15, 20, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![64, 20, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-15, 20, 1], ![114, -73, 103], ![2394, -348, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -20, 79]], ![![-1, 0, 1], ![-82, -27, 103], ![6, -12, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [63, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 78], [0, 1]]
 g := ![![[10, 9], [46, 76], [70, 67], [42, 49], [4], [1]], ![[28, 70], [40, 3], [46, 12], [61, 30], [4], [1]]]
 h' := ![![[2, 78], [25, 3], [14, 47], [40, 15], [4, 72], [16, 2], [0, 1]], ![[0, 1], [31, 76], [29, 32], [70, 64], [69, 7], [20, 77], [2, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [7, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [63, 77, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1233, 15, 139]
  a := ![13, -1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-97, -35, 139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-24, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-24, 1, 0]] 
 ![![79, 0, 0], ![55, 1, 0], ![49, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-24, 1, 0], ![0, -26, 5], ![114, -18, -21]]]
  hmulB := by decide  
  f := ![![![1681, -70, 0], ![5530, 0, 0]], ![![1177, -49, 0], ![3872, 0, 0]], ![![1039, -38, -1], ![3418, 16, 0]]]
  g := ![![![1, 0, 0], ![-55, 79, 0], ![-49, 0, 79]], ![![-1, 1, 0], ![15, -26, 5], ![27, -18, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-15, 20, 1]] ![![79, 0, 0], ![-24, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1896, 79, 0]], ![![-1185, 1580, 79], ![474, -553, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-24, 1, 0]]], ![![![-15, 20, 1]], ![![6, -7, 1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB182I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB182I1 : PrimesBelowBoundCertificateInterval O 31 79 182 where
  m := 11
  g := ![1, 2, 2, 1, 2, 2, 1, 2, 3, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB182I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
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
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![389017]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
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
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
  β := ![I41N1, I43N1, I53N1, I59N1, I67N1, I71N0, I71N1, I71N2, I79N1]
  Il := ![[], [I41N1], [I43N1], [], [I53N1], [I59N1], [], [I67N1], [I71N0, I71N1, I71N2], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
