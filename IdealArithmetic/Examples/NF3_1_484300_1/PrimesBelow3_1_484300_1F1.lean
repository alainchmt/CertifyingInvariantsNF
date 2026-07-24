
import IdealArithmetic.Examples.NF3_1_484300_1.RI3_1_484300_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [8, 31, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 2, 23], [10, 34, 14], [0, 1]]
 g := ![![[36, 5, 26], [26, 21], [0, 6, 9], [18, 1], []], ![[36, 10, 15, 2], [24, 36], [13, 22, 18, 32], [11, 9], [31, 11]], ![[13, 25, 18, 15], [23, 12], [26, 1, 29, 18], [33, 4], [3, 11]]]
 h' := ![![[8, 2, 23], [14, 25, 27], [0, 5, 24], [4, 26, 34], [0, 0, 1], [0, 1]], ![[10, 34, 14], [19, 8, 13], [27, 22, 6], [24, 32, 15], [1, 19, 34], [8, 2, 23]], ![[0, 1], [22, 4, 34], [24, 10, 7], [36, 16, 25], [2, 18, 2], [10, 34, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 8], []]
 b := ![[], [32, 30, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [8, 31, 19, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-239575, -52281, -1998]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6475, -1413, -54]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [34, 12, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 34, 33], [22, 6, 8], [0, 1]]
 g := ![![[24, 18, 20], [8, 40], [31, 20], [8, 26, 1], []], ![[24, 1, 38, 10], [2, 8], [24, 1], [33, 30, 26, 40], [13, 23]], ![[9, 2, 22, 4], [24, 10], [10, 32], [5, 9, 18, 23], [38, 23]]]
 h' := ![![[4, 34, 33], [14, 27, 15], [32, 11, 9], [15, 4, 26], [0, 0, 1], [0, 1]], ![[22, 6, 8], [5, 30, 38], [14, 38, 7], [25, 40, 1], [25, 31, 6], [4, 34, 33]], ![[0, 1], [9, 25, 29], [13, 33, 25], [5, 38, 14], [12, 10, 34], [22, 6, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 26], []]
 b := ![[], [15, 18, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [34, 12, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1632948, 393846, 81344]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39828, 9606, 1984]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [33, 41, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 42, 3], [19, 0, 40], [0, 1]]
 g := ![![[41, 22, 11], [7, 17, 1], [21, 25], [3, 42, 1], []], ![[31, 11, 5, 34], [9, 29, 1, 37], [15, 15], [6, 29], [28, 9]], ![[9, 15, 12, 23], [12, 42, 0, 13], [3, 6], [42, 14, 5, 40], [34, 9]]]
 h' := ![![[23, 42, 3], [27, 33, 22], [35, 9, 1], [30, 39, 5], [0, 0, 1], [0, 1]], ![[19, 0, 40], [8, 17, 13], [19, 5, 27], [27, 31, 31], [35, 14], [23, 42, 3]], ![[0, 1], [37, 36, 8], [4, 29, 15], [19, 16, 7], [13, 29, 42], [19, 0, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 13], []]
 b := ![[], [17, 18, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [33, 41, 1, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14026030680, -3145980233, -324927608]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-326186760, -73162331, -7556456]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44347568, -3398125, 1739261]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![44347568, -3398125, 1739261]] 
 ![![47, 0, 0], ![0, 47, 0], ![24, 37, 1]] where
  M :=![![![44347568, -3398125, 1739261], ![-215587967, 16519392, -8455114], ![334565244, -25636006, 13121267]]]
  hmulB := by decide  
  f := ![![![-2660, -153, 254]], ![![-31141, -6724, -205]], ![![-25725, -5568, -178]]]
  g := ![![![55432, -1441506, 1739261], ![-269473, 7007630, -8455114], ![418188, -10874955, 13121267]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [18, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 46], [0, 1]]
 g := ![![[13, 34], [24, 1], [32, 27], [12, 1], [1]], ![[0, 13], [25, 46], [12, 20], [13, 46], [1]]]
 h' := ![![[1, 46], [38, 9], [35, 1], [19, 36], [29, 1], [0, 1]], ![[0, 1], [0, 38], [36, 46], [8, 11], [30, 46], [1, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [45, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [18, 46, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-615, -1988, -1089]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![543, 815, -1089]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2660, 153, -254]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![2660, 153, -254]] 
 ![![47, 0, 0], ![29, 1, 0], ![2, 0, 1]] where
  M :=![![![2660, 153, -254], ![31141, 6724, 205], ![-6982, 9236, 6877]]]
  hmulB := by decide  
  f := ![![![-44347568, 3398125, -1739261]], ![![-22776415, 1745239, -893265]], ![![-9005540, 690048, -353187]]]
  g := ![![![-27, 153, -254], ![-3495, 6724, 205], ![-6140, 9236, 6877]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![44347568, -3398125, 1739261]] ![![2660, 153, -254]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-1, 17, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-1, 17, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![52, 17, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-1, 17, 1], ![-105, -17, 52], ![-2120, -318, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -17, 53]], ![![-1, 0, 1], ![-53, -17, 52], ![-40, -6, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [4, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 52], [0, 1]]
 g := ![![[30, 40], [25], [33, 16], [29], [39, 1]], ![[0, 13], [25], [21, 37], [29], [25, 52]]]
 h' := ![![[39, 52], [46, 26], [27, 5], [52, 4], [3, 33], [0, 1]], ![[0, 1], [0, 27], [10, 48], [49, 49], [18, 20], [39, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [17, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [4, 14, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1154, -522, -171]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![146, 45, -171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![1, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![1, 1, 0]] 
 ![![53, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![1, 1, 0], ![1, 1, 3], ![-122, -16, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![53, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![-18, 18, 0]]]
  g := ![![![1, 0, 0], ![-1, 53, 0], ![0, 0, 53]], ![![0, 1, 0], ![0, 1, 3], ![-2, -16, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-1, 17, 1]] ![![53, 0, 0], ![1, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![53, 53, 0]], ![![-53, 901, 53], ![-106, 0, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![1, 1, 0]]], ![![![-1, 17, 1]], ![![-2, 0, 1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![15, 17, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![15, 17, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![15, 17, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![15, 17, 1], ![-105, -1, 52], ![-2120, -318, 16]]]
  hmulB := by decide  
  f := ![![![-14, -17, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -17, 59]], ![![0, 0, 1], ![-15, -15, 52], ![-40, -10, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [9, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 58], [0, 1]]
 g := ![![[29, 46], [10, 45], [7], [51, 27], [34, 1]], ![[0, 13], [6, 14], [7], [25, 32], [9, 58]]]
 h' := ![![[34, 58], [28, 20], [47, 24], [13, 19], [48, 26], [0, 1]], ![[0, 1], [0, 39], [37, 35], [10, 40], [47, 33], [34, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [25, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [9, 25, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23906, -3639, 1018]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-664, -355, 1018]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![7, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![7, 1, 0]] 
 ![![59, 0, 0], ![7, 1, 0], ![43, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![7, 1, 0], ![1, 7, 3], ![-122, -16, 8]]]
  hmulB := by decide  
  f := ![![![-101, -714, -306], ![0, 6018, 0]], ![![-12, -84, -36], ![1, 708, 0]], ![![-78, -521, -223], ![37, 4386, 0]]]
  g := ![![![1, 0, 0], ![-7, 59, 0], ![-43, 0, 59]], ![![0, 1, 0], ![-3, 7, 3], ![-6, -16, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![15, 17, 1]] ![![59, 0, 0], ![7, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![413, 59, 0]], ![![885, 1003, 59], ![0, 118, 59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![7, 1, 0]]], ![![![15, 17, 1]], ![![0, 2, 1]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![1, -31, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![1, -31, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![1, 30, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![1, -31, 1], ![-153, -15, -92], ![3736, 450, -46]]]
  hmulB := by decide  
  f := ![![![0, 31, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -30, 61]], ![![0, -1, 1], ![-1, 45, -92], ![62, 30, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [27, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 60], [0, 1]]
 g := ![![[15, 52], [13], [8, 9], [20, 46], [22, 1]], ![[0, 9], [13], [23, 52], [56, 15], [44, 60]]]
 h' := ![![[22, 60], [6, 33], [28, 14], [9, 3], [16, 30], [0, 1]], ![[0, 1], [0, 28], [31, 47], [14, 58], [5, 31], [22, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [51, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [27, 39, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2472, -565, -578]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50, 275, -578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-30, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-30, 1, 0]] 
 ![![61, 0, 0], ![31, 1, 0], ![46, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-30, 1, 0], ![1, -30, 3], ![-122, -16, -29]]]
  hmulB := by decide  
  f := ![![![-11, 1259, -126], ![61, 2562, 0]], ![![10, 629, -63], ![62, 1281, 0]], ![![4, 949, -95], ![71, 1932, 0]]]
  g := ![![![1, 0, 0], ![-31, 61, 0], ![-46, 0, 61]], ![![-1, 1, 0], ![13, -30, 3], ![28, -16, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![1, -31, 1]] ![![61, 0, 0], ![-30, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1830, 61, 0]], ![![61, -1891, 61], ![-183, 915, -122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-30, 1, 0]]], ![![![1, -31, 1]], ![![-3, 15, -2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![20, 1, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![20, 1, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![20, 1, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![20, 1, 1], ![-121, 4, 4], ![-168, -62, 5]]]
  hmulB := by decide  
  f := ![![![-19, -1, -1], ![67, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -1, 67]], ![![0, 0, 1], ![-3, 0, 4], ![-4, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [28, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 66], [0, 1]]
 g := ![![[39, 39], [33, 36], [25], [39], [65], [1]], ![[63, 28], [50, 31], [25], [39], [65], [1]]]
 h' := ![![[47, 66], [14, 46], [46, 6], [3, 62], [36, 21], [39, 47], [0, 1]], ![[0, 1], [32, 21], [60, 61], [36, 5], [18, 46], [37, 20], [47, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [66, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [28, 20, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3047, -1824, -417]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![79, -21, -417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-4, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-4, 1, 0]] 
 ![![67, 0, 0], ![63, 1, 0], ![62, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-4, 1, 0], ![1, -4, 3], ![-122, -16, -3]]]
  hmulB := by decide  
  f := ![![![-1783, 7196, -5400], ![268, 120600, 0]], ![![-1679, 6765, -5076], ![202, 113364, 0]], ![![-1650, 6659, -4997], ![247, 111600, 0]]]
  g := ![![![1, 0, 0], ![-63, 67, 0], ![-62, 0, 67]], ![![-1, 1, 0], ![1, -4, 3], ![16, -16, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![20, 1, 1]] ![![67, 0, 0], ![-4, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-268, 67, 0]], ![![1340, 67, 67], ![-201, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-4, 1, 0]]], ![![![20, 1, 1]], ![![-3, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![37, -15, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![37, -15, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![37, 56, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![37, -15, 1], ![-137, 21, -44], ![1784, 194, 6]]]
  hmulB := by decide  
  f := ![![![-36, 15, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -56, 71]], ![![0, -1, 1], ![21, 35, -44], ![22, -2, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [61, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 70], [0, 1]]
 g := ![![[37, 18], [69, 5], [43, 15], [5], [12], [1]], ![[23, 53], [2, 66], [55, 56], [5], [12], [1]]]
 h' := ![![[15, 70], [51, 36], [4, 17], [28, 50], [7, 54], [10, 15], [0, 1]], ![[0, 1], [23, 35], [46, 54], [68, 21], [36, 17], [22, 56], [15, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [59, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [61, 56, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4794, -4600, -2060]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1006, 1560, -2060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-27, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-27, 1, 0]] 
 ![![71, 0, 0], ![44, 1, 0], ![65, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-27, 1, 0], ![1, -27, 3], ![-122, -16, -26]]]
  hmulB := by decide  
  f := ![![![-560, 20971, -2331], ![568, 55167, 0]], ![![-345, 12982, -1443], ![356, 34151, 0]], ![![-518, 19199, -2134], ![506, 50505, 0]]]
  g := ![![![1, 0, 0], ![-44, 71, 0], ![-65, 0, 71]], ![![-1, 1, 0], ![14, -27, 3], ![32, -16, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![37, -15, 1]] ![![71, 0, 0], ![-27, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1917, 71, 0]], ![![2627, -1065, 71], ![-1136, 426, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-27, 1, 0]]], ![![![37, -15, 1]], ![![-16, 6, -1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [52, 22, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 51, 28], [13, 21, 45], [0, 1]]
 g := ![![[19, 61, 16], [45, 54], [1, 65], [62, 4, 9], [47, 1], []], ![[59, 35, 63, 63], [27, 57], [], [9, 66, 36, 15], [67, 3], [65, 54]], ![[2, 16, 46, 29], [44, 27], [12, 65], [50, 53, 51, 22], [37, 46], [48, 54]]]
 h' := ![![[34, 51, 28], [65, 14, 4], [19, 35, 28], [61, 18, 49], [38, 9, 70], [0, 0, 1], [0, 1]], ![[13, 21, 45], [40, 43, 38], [38, 8, 35], [29, 53], [8, 68, 43], [39, 33, 21], [34, 51, 28]], ![[0, 1], [64, 16, 31], [69, 30, 10], [6, 2, 24], [55, 69, 33], [9, 40, 51], [13, 21, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 6], []]
 b := ![[], [11, 20, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [52, 22, 26, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1338820, 419020, 427780]
  a := ![4, -10, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18340, 5740, 5860]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [9, 16, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 58, 5], [74, 20, 74], [0, 1]]
 g := ![![[19, 16, 11], [4, 19, 13], [77, 37, 73], [12, 72, 64], [61, 1], []], ![[26, 55, 2, 11], [5, 61, 15, 62], [41, 2, 30, 67], [50, 5, 28, 18], [18, 5], [51, 25]], ![[3, 76, 43, 47], [27, 12, 31, 33], [62, 64, 49, 15], [48, 54, 68, 28], [28, 46], [61, 25]]]
 h' := ![![[66, 58, 5], [43, 10, 66], [18, 66, 48], [50, 45, 51], [4, 42, 71], [0, 0, 1], [0, 1]], ![[74, 20, 74], [49, 63, 27], [13, 55, 26], [1, 38, 60], [40, 76, 50], [26, 58, 20], [66, 58, 5]], ![[0, 1], [11, 6, 65], [53, 37, 5], [40, 75, 47], [36, 40, 37], [29, 21, 58], [74, 20, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 63], []]
 b := ![[], [20, 9, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [9, 16, 18, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148110859, 33092231, 3605718]
  a := ![14, -1, 29]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1874821, 418889, 45642]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB197I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB197I1 : PrimesBelowBoundCertificateInterval O 31 79 197 where
  m := 11
  g := ![1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB197I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0]
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
    · exact ![68921]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![493039]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
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
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I47N1, I53N1, I59N1, I61N1, I67N1, I71N1]
  Il := ![[], [], [], [I47N1], [I53N1], [I59N1], [I61N1], [I67N1], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
