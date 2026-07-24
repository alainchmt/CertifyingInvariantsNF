
import IdealArithmetic.Examples.NF3_1_547128_1.RI3_1_547128_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [17, 11, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 9, 1], [8, 27, 36], [0, 1]]
 g := ![![[29, 7, 12], [8, 25], [10, 22, 25], [33, 1], []], ![[28, 12], [35, 30], [14, 13, 2, 11], [14, 26], [14, 1]], ![[10, 11, 8, 25], [19, 33], [2, 4, 17, 9], [19, 7], [16, 1]]]
 h' := ![![[25, 9, 1], [15, 33, 7], [15, 33, 5], [31, 27, 5], [0, 0, 1], [0, 1]], ![[8, 27, 36], [34, 30], [0, 27, 20], [14, 10, 14], [17, 20, 27], [25, 9, 1]], ![[0, 1], [7, 11, 30], [16, 14, 12], [21, 0, 18], [14, 17, 9], [8, 27, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 25], []]
 b := ![[], [33, 7, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [17, 11, 4, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-346209, -40848, -18870]
  a := ![-1, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9357, -1104, -510]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![15, 18, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![15, 18, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![15, 18, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![15, 18, 1], ![180, 93, 176], ![2478, 120, -48]]]
  hmulB := by decide  
  f := ![![![-14, -18, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -18, 41]], ![![0, 0, 1], ![-60, -75, 176], ![78, 24, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [32, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 40], [0, 1]]
 g := ![![[11, 9], [37], [10], [12, 2], [1]], ![[0, 32], [37], [10], [5, 39], [1]]]
 h' := ![![[17, 40], [10, 38], [28, 18], [26, 16], [9, 17], [0, 1]], ![[0, 1], [0, 3], [6, 23], [11, 25], [11, 24], [17, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [8, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [32, 24, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7366, 1788, 1261]
  a := ![2, 2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-641, -510, 1261]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-12, 1, 0]] 
 ![![41, 0, 0], ![29, 1, 0], ![7, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-12, 1, 0], ![2, -8, 10], ![144, 6, -16]]]
  hmulB := by decide  
  f := ![![![1229, -5429, 6800], ![-451, -27880, 0]], ![![865, -3832, 4800], ![-327, -19680, 0]], ![![211, -927, 1161], ![-73, -4760, 0]]]
  g := ![![![1, 0, 0], ![-29, 41, 0], ![-7, 0, 41]], ![![-1, 1, 0], ![4, -8, 10], ![2, 6, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![15, 18, 1]] ![![41, 0, 0], ![-12, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![-492, 41, 0]], ![![615, 738, 41], ![0, -123, 164]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![-12, 1, 0]]], ![![![15, 18, 1]], ![![0, -3, 4]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [11, 1, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 14, 22], [35, 28, 21], [0, 1]]
 g := ![![[25, 17, 14], [41, 40, 9], [4, 13], [22, 18, 1], []], ![[26, 28], [40, 42, 15, 34], [3, 23], [12, 11, 24, 5], [40, 11]], ![[6, 19, 3, 36], [31, 1, 30, 41], [23, 4], [34, 42, 9, 31], [41, 11]]]
 h' := ![![[26, 14, 22], [22, 1, 33], [40, 37, 3], [16, 38, 23], [0, 0, 1], [0, 1]], ![[35, 28, 21], [10, 20], [33, 26, 38], [25, 28, 18], [21, 8, 28], [26, 14, 22]], ![[0, 1], [14, 22, 10], [2, 23, 2], [13, 20, 2], [0, 35, 14], [35, 28, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 33], []]
 b := ![[], [39, 0, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [11, 1, 25, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43373814136, -5147901864, -1853789211]
  a := ![-65, -129, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1008693352, -119718648, -43111377]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46045397307017, -606042844121, -2948601375330]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![46045397307017, -606042844121, -2948601375330]] 
 ![![47, 0, 0], ![0, 47, 0], ![13, 3, 1]] where
  M :=![![![46045397307017, -606042844121, -2948601375330], ![-425810683735762, 25929617678553, 5733977060110], ![248870387234196, -39019473568686, 21932156305531]]]
  hmulB := by decide  
  f := ![![![16860195621470175949993449, 2730738293923201146894673, 1552788735811251554620940]], ![![229063054544666626159204706, 37099881212030489865297781, 21096227995987005250462970]], ![![23884683088416392633054781, 3868449703199304468986030, 2199729332374168538626901]]]
  g := ![![![1795259897581, 175314069827, -2948601375330], ![-10645795436536, 185695457409, 5733977060110], ![-771226483781, -2230126435857, 21932156305531]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [3, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 46], [0, 1]]
 g := ![![[25, 16], [41, 1], [12, 2], [24, 32], [1]], ![[0, 31], [13, 46], [3, 45], [21, 15], [1]]]
 h' := ![![[19, 46], [18, 4], [11, 1], [22, 40], [44, 19], [0, 1]], ![[0, 1], [0, 43], [30, 46], [30, 7], [29, 28], [19, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [8, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [3, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4321, 1812, 651]
  a := ![-2, -3, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-272, -3, 651]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16860195621470175949993449, 2730738293923201146894673, 1552788735811251554620940]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![16860195621470175949993449, 2730738293923201146894673, 1552788735811251554620940]] 
 ![![47, 0, 0], ![21, 1, 0], ![37, 0, 1]] where
  M :=![![![16860195621470175949993449, 2730738293923201146894673, 1552788735811251554620940], ![229063054544666626159204706, 37099881212030489865297781, 21096227995987005250462970], ![216208398442458287926045752, 35017894593274225536819318, 19912341068078635354003217]]]
  hmulB := by decide  
  f := ![![![46045397307017, -606042844121, -2948601375330]], ![![11513673610885, 280908892596, -1195460677060]], ![![41543618884975, -1307299123429, -1854597757057]]]
  g := ![![![-2083797697360284162888712, 2730738293923201146894673, 1552788735811251554620940], ![-28310529505521124580408055, 37099881212030489865297781, 21096227995987005250462970], ![-26721787394366169286069765, 35017894593274225536819318, 19912341068078635354003217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![46045397307017, -606042844121, -2948601375330]] ![![16860195621470175949993449, 2730738293923201146894673, 1552788735811251554620940]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 1, -8]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![89, 1, -8]] 
 ![![53, 0, 0], ![17, 1, 0], ![44, 0, 1]] where
  M :=![![![89, 1, -8], ![-1150, 45, 42], ![1056, -90, 13]]]
  hmulB := by decide  
  f := ![![![-4365, -707, -402]], ![![-2519, -408, -232]], ![![-4680, -758, -431]]]
  g := ![![![8, 1, -8], ![-71, 45, 42], ![38, -90, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-13, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-13, 1, 0]] 
 ![![53, 0, 0], ![40, 1, 0], ![15, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-13, 1, 0], ![2, -9, 10], ![144, 6, -17]]]
  hmulB := by decide  
  f := ![![![-173, 898, -1000], ![106, 5300, 0]], ![![-136, 674, -750], ![54, 3975, 0]], ![![-47, 254, -283], ![38, 1500, 0]]]
  g := ![![![1, 0, 0], ![-40, 53, 0], ![-15, 0, 53]], ![![-1, 1, 0], ![4, -9, 10], ![3, 6, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-4, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-4, 1, 0]] 
 ![![53, 0, 0], ![49, 1, 0], ![32, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-4, 1, 0], ![2, 0, 10], ![144, 6, -8]]]
  hmulB := by decide  
  f := ![![![-1317, -2, -6630], ![106, 35139, 0]], ![![-1215, -2, -6120], ![107, 32436, 0]], ![![-792, -2, -4003], ![106, 21216, 0]]]
  g := ![![![1, 0, 0], ![-49, 53, 0], ![-32, 0, 53]], ![![-1, 1, 0], ![-6, 0, 10], ![2, 6, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![89, 1, -8]] ![![53, 0, 0], ![-13, 1, 0]]
  ![![53, 0, 0], ![-6, 22, 1]] where
 M := ![![![4717, 53, -424], ![-2307, 32, 146]]]
 hmul := by decide  
 g := ![![![![89, 1, -8], ![0, 0, 0]], ![![-39, -16, 2], ![40, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-6, 22, 1]] ![![53, 0, 0], ![-4, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-212, 53, 0]], ![![-318, 1166, 53], ![212, 0, 212]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-4, 1, 0]]], ![![![-6, 22, 1]], ![![4, 0, 4]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-29, 29, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-29, 29, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![30, 29, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-29, 29, 1], ![202, 93, 286], ![4062, 186, -136]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -29, 59]], ![![-1, 0, 1], ![-142, -139, 286], ![138, 70, -136]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [4, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 58], [0, 1]]
 g := ![![[19, 15], [39, 53], [53], [8, 41], [42, 1]], ![[0, 44], [23, 6], [53], [19, 18], [25, 58]]]
 h' := ![![[42, 58], [21, 29], [45, 17], [27, 17], [9, 49], [0, 1]], ![[0, 1], [0, 30], [51, 42], [33, 42], [2, 10], [42, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [41, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [4, 17, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1476, 471, 120]
  a := ![-1, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -51, 120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![9, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![9, 1, 0]] 
 ![![59, 0, 0], ![9, 1, 0], ![18, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![9, 1, 0], ![2, 13, 10], ![144, 6, 5]]]
  hmulB := by decide  
  f := ![![![4946, 33465, 25760], ![1357, -151984, 0]], ![![748, 5092, 3920], ![237, -23128, 0]], ![![1503, 10209, 7859], ![453, -46368, 0]]]
  g := ![![![1, 0, 0], ![-9, 59, 0], ![-18, 0, 59]], ![![0, 1, 0], ![-5, 13, 10], ![0, 6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-29, 29, 1]] ![![59, 0, 0], ![9, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![531, 59, 0]], ![![-1711, 1711, 59], ![-59, 354, 295]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![9, 1, 0]]], ![![![-29, 29, 1]], ![![-1, 6, 5]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3960414174792149, -1327347254200375, 1715102544068578]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-3960414174792149, -1327347254200375, 1715102544068578]] 
 ![![61, 0, 0], ![30, 1, 0], ![8, 0, 1]] where
  M :=![![![-3960414174792149, -1327347254200375, 1715102544068578], ![244320071837474482, 1020812072817819, -20133882718278062], ![-386659694628671892, 12617147003620686, 16784897738626553]]]
  hmulB := by decide  
  f := ![![![-271166384262774856698678968138439, -43919088850197113217252240961883, -24973856559393008088055478281868]], ![![-193755164756331690034014137683048, -31381287615177618928091607057929, -17844445230265399056753522048318]], ![![-92568200340324266144843113434192, -14992680698614355444232739554898, -8525337547076517070928084181683]]]
  g := ![![![362937427847057, -1327347254200375, 1715102544068578], ![6143717563920728, 1020812072817819, -20133882718278062], ![-14745135846660736, 12617147003620686, 16784897738626553]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-29, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-29, 1, 0]] 
 ![![61, 0, 0], ![32, 1, 0], ![7, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-29, 1, 0], ![2, -25, 10], ![144, 6, -33]]]
  hmulB := by decide  
  f := ![![![334, -5247, 2100], ![-183, -12810, 0]], ![![163, -2748, 1100], ![-121, -6710, 0]], ![![64, -603, 241], ![33, -1470, 0]]]
  g := ![![![1, 0, 0], ![-32, 61, 0], ![-7, 0, 61]], ![![-1, 1, 0], ![12, -25, 10], ![3, 6, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-1, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-1, 1, 0]] 
 ![![61, 0, 0], ![60, 1, 0], ![31, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-1, 1, 0], ![2, 3, 10], ![144, 6, -5]]]
  hmulB := by decide  
  f := ![![![5882, 8819, 29400], ![61, -179340, 0]], ![![5784, 8672, 28910], ![62, -176351, 0]], ![![2990, 4481, 14941], ![79, -91140, 0]]]
  g := ![![![1, 0, 0], ![-60, 61, 0], ![-31, 0, 61]], ![![-1, 1, 0], ![-8, 3, 10], ![-1, 6, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-3960414174792149, -1327347254200375, 1715102544068578]] ![![61, 0, 0], ![-29, 1, 0]]
  ![![61, 0, 0], ![23, -30, 1]] where
 M := ![![![-241585264662321089, -80968182506222875, 104621255188183258], ![359172082906446803, 39513882444628694, -69871856496266824]]]
 hmul := by decide  
 g := ![![![![-3739147986760093, -1615955325546535, 1724722813113450], ![-586836411737192, 0, 0]], ![![5375257386850871, 1316650581242174, -1167736337649808], ![1360060100371464, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![23, -30, 1]] ![![61, 0, 0], ![-1, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-61, 61, 0]], ![![1403, -1830, 61], ![61, -61, -305]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-1, 1, 0]]], ![![![23, -30, 1]], ![![1, -1, -5]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4446691963531, -205972534983, -128539865048]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![4446691963531, -205972534983, -128539865048]] 
 ![![67, 0, 0], ![0, 67, 0], ![50, 65, 1]] where
  M :=![![![4446691963531, -205972534983, -128539865048], ![-18921685636878, 2851562633311, -1545565889638], ![-15006500422080, -2778313590474, 4113723318031]]]
  hmulB := by decide  
  f := ![![![110992134049597744409287, 17976687671851869858675, 10222143288562834651046]], ![![1507942008896751929467974, 244231744468382231750263, 138878303564267359982566]], ![![1567002327919690578288248, 253797367455691101368141, 144317635359175759824673]]]
  g := ![![![162293809193, 121628637211, -128539865048], ![870994161866, 1541990230743, -1545565889638], ![-3293920392890, -4032392974067, 4113723318031]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [40, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 66], [0, 1]]
 g := ![![[38, 62], [4, 9], [26], [33], [39], [1]], ![[0, 5], [59, 58], [26], [33], [39], [1]]]
 h' := ![![[21, 66], [41, 14], [42, 64], [12, 19], [40, 10], [27, 21], [0, 1]], ![[0, 1], [0, 53], [46, 3], [9, 48], [49, 57], [66, 46], [21, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [48, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [40, 46, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51576, 6722, 4813]
  a := ![2, 23, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2822, -4569, 4813]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2020240576207341733, -1878225508613089615, 1832354449056121038]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![2020240576207341733, -1878225508613089615, 1832354449056121038]] 
 ![![67, 0, 0], ![24, 1, 0], ![0, 0, 1]] where
  M :=![![![2020240576207341733, -1878225508613089615, 1832354449056121038], ![260102589646855250242, 5501465236091709501, -26111672882355380302], ![-479352880432682702892, 10718900336994914766, 26024332652164789535]]]
  hmulB := by decide  
  f := ![![![-423060380636551011637579874872030211367, -68520390153410234385422696863958626133, -38962975778520326662963042069141181692]], ![![-237330722801357787873722991770342872966, -38438942680644172155331248350413713929, -21857662941858341449455041940632983510]], ![![-80972491691638156894374351530267872392, -13114597765115004869673025164379790106, -7457397045217806180038156209529348389]]]
  g := ![![![702950041536141679, -1878225508613089615, 1832354449056121038], ![1911454089263495854, 5501465236091709501, -26111672882355380302], ![-10994126694336726228, 10718900336994914766, 26024332652164789535]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![4446691963531, -205972534983, -128539865048]] ![![2020240576207341733, -1878225508613089615, 1832354449056121038]]
  ![![67, 0, 0]] where
 M := ![![![17025352350601751083625685442153, -10862847018427696667967713302816, 10181039052110200608884359297364]]]
 hmul := by decide  
 g := ![![![![254109736576145538561577394659, -162132045051159651760712138848, 151955806747913441923647153692]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-9, 5, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-9, 5, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![62, 5, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-9, 5, 1], ![154, 17, 46], ![606, 42, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -5, 71]], ![![-1, 0, 1], ![-38, -3, 46], ![26, 2, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [35, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 70], [0, 1]]
 g := ![![[22, 9], [2, 60], [8, 64], [49], [50], [1]], ![[50, 62], [23, 11], [2, 7], [49], [50], [1]]]
 h' := ![![[11, 70], [1, 68], [4, 42], [63, 8], [43, 64], [36, 11], [0, 1]], ![[0, 1], [39, 3], [40, 29], [9, 63], [37, 7], [15, 60], [11, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [48, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [35, 60, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6721, 1028, 163]
  a := ![-2, -1, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-237, 3, 163]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![25, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![25, 1, 0]] 
 ![![71, 0, 0], ![25, 1, 0], ![20, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![25, 1, 0], ![2, 29, 10], ![144, 6, 21]]]
  hmulB := by decide  
  f := ![![![5522, 97045, 33480], ![3337, -237708, 0]], ![![1931, 34145, 11780], ![1208, -83638, 0]], ![![1540, 27336, 9431], ![984, -66960, 0]]]
  g := ![![![1, 0, 0], ![-25, 71, 0], ![-20, 0, 71]], ![![0, 1, 0], ![-13, 29, 10], ![-6, 6, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-9, 5, 1]] ![![71, 0, 0], ![25, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1775, 71, 0]], ![![-639, 355, 71], ![-71, 142, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![25, 1, 0]]], ![![![-9, 5, 1]], ![![-1, 2, 1]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-14, 22, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-14, 22, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![59, 22, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-14, 22, 1], ![188, 80, 216], ![3054, 144, -93]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -22, 73]], ![![-1, 0, 1], ![-172, -64, 216], ![117, 30, -93]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [32, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 72], [0, 1]]
 g := ![![[9, 16], [9], [50], [50, 72], [16], [1]], ![[0, 57], [9], [50], [46, 1], [16], [1]]]
 h' := ![![[4, 72], [16, 69], [42, 3], [6, 14], [1, 27], [41, 4], [0, 1]], ![[0, 1], [0, 4], [54, 70], [62, 59], [36, 46], [57, 69], [4, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [13, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [32, 69, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3224, 2265, 1480]
  a := ![2, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1152, -415, 1480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![3, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![3, 1, 0]] 
 ![![73, 0, 0], ![3, 1, 0], ![20, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![3, 1, 0], ![2, 7, 10], ![144, 6, -1]]]
  hmulB := by decide  
  f := ![![![390, 1371, 1960], ![73, -14308, 0]], ![![13, 55, 80], ![74, -584, 0]], ![![105, 375, 537], ![65, -3920, 0]]]
  g := ![![![1, 0, 0], ![-3, 73, 0], ![-20, 0, 73]], ![![0, 1, 0], ![-3, 7, 10], ![2, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-14, 22, 1]] ![![73, 0, 0], ![3, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![219, 73, 0]], ![![-1022, 1606, 73], ![146, 146, 219]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![3, 1, 0]]], ![![![-14, 22, 1]], ![![2, 2, 3]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [66, 7, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 33, 53], [19, 45, 26], [0, 1]]
 g := ![![[29, 23, 38], [55, 15, 44], [14, 4, 36], [66, 43, 36], [1, 1], []], ![[16, 62, 69, 61], [48, 13, 64, 33], [56, 46, 61, 3], [51, 74, 24, 57], [42, 50], [66, 44]], ![[70, 57, 21, 52], [72, 3, 18, 40], [69, 29, 63, 76], [2, 24, 48, 44], [31, 62], [14, 44]]]
 h' := ![![[61, 33, 53], [4, 70, 14], [24, 75, 53], [68, 29, 73], [13, 6, 73], [0, 0, 1], [0, 1]], ![[19, 45, 26], [45, 16, 74], [16, 9, 40], [38, 78, 3], [2, 30, 48], [76, 28, 45], [61, 33, 53]], ![[0, 1], [9, 72, 70], [50, 74, 65], [47, 51, 3], [29, 43, 37], [69, 51, 33], [19, 45, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 23], []]
 b := ![[], [24, 5, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [66, 7, 78, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18749544, -1752220, -613040]
  a := ![-5, -10, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-237336, -22180, -7760]
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



lemma PB210I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB210I1 : PrimesBelowBoundCertificateInterval O 31 79 210 where
  m := 11
  g := ![1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB210I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
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
      exact NI41N1
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
      exact NI53N2
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N1, I47N1, I53N0, I53N1, I53N2, I59N1, I61N0, I61N1, I61N2, I67N1, I71N1, I73N1]
  Il := ![[], [I41N1], [], [I47N1], [I53N0, I53N1, I53N2], [I59N1], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
