
import IdealArithmetic.Examples.NF3_1_344763_1.RI3_1_344763_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [6, 31, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 31, 21], [10, 5, 16], [0, 1]]
 g := ![![[14, 35, 27], [17, 28], [30, 2, 36], [0, 1], []], ![[36, 34, 25, 7], [30, 27], [11, 25, 25, 26], [24, 25], [7, 34]], ![[20, 2, 5, 3], [11, 26], [14, 33, 22, 26], [14, 36], [12, 34]]]
 h' := ![![[27, 31, 21], [34, 23, 8], [5, 20, 18], [0, 31, 6], [0, 0, 1], [0, 1]], ![[10, 5, 16], [9, 7, 5], [35, 12, 29], [1, 6, 15], [21, 32, 5], [27, 31, 21]], ![[0, 1], [7, 7, 24], [6, 5, 27], [34, 0, 16], [28, 5, 31], [10, 5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 3], []]
 b := ![[], [20, 1, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [6, 31, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12876, -370, -370]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-348, -10, -10]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-4, -18, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-4, -18, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![37, 23, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-4, -18, 1], ![113, -4, -18], ![-2034, 113, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -23, 41]], ![![-1, -1, 1], ![19, 10, -18], ![-46, 5, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [11, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 40], [0, 1]]
 g := ![![[21, 8], [16], [10], [11, 20], [1]], ![[18, 33], [16], [10], [24, 21], [1]]]
 h' := ![![[15, 40], [31, 7], [17, 4], [2, 25], [30, 15], [0, 1]], ![[0, 1], [13, 34], [36, 37], [8, 16], [9, 26], [15, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [25, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [11, 26, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1370, 969, 76]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, -19, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![18, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![18, 1, 0]] 
 ![![41, 0, 0], ![18, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![18, 1, 0], ![0, 18, 1], ![113, 0, 18]]]
  hmulB := by decide  
  f := ![![![181, 10, 0], ![-410, 0, 0]], ![![90, 5, 0], ![-204, 0, 0]], ![![8, 0, 0], ![-18, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 41, 0], ![-4, 0, 41]], ![![0, 1, 0], ![-8, 18, 1], ![1, 0, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-4, -18, 1]] ![![41, 0, 0], ![18, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![738, 41, 0]], ![![-164, -738, 41], ![41, -328, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![18, 1, 0]]], ![![![-4, -18, 1]], ![![1, -8, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![21, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![21, 1, 0]] 
 ![![43, 0, 0], ![21, 1, 0], ![32, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![21, 1, 0], ![0, 21, 1], ![113, 0, 21]]]
  hmulB := by decide  
  f := ![![![190, 9, 0], ![-387, 0, 0]], ![![84, 4, 0], ![-171, 0, 0]], ![![158, 7, 0], ![-322, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 43, 0], ![-32, 0, 43]], ![![0, 1, 0], ![-11, 21, 1], ![-13, 0, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-18, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-18, 1, 0]] 
 ![![43, 0, 0], ![25, 1, 0], ![20, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-18, 1, 0], ![0, -18, 1], ![113, 0, -18]]]
  hmulB := by decide  
  f := ![![![361, -20, 0], ![860, 0, 0]], ![![199, -11, 0], ![474, 0, 0]], ![![188, -10, 0], ![448, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 43, 0], ![-20, 0, 43]], ![![-1, 1, 0], ![10, -18, 1], ![11, 0, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-3, 1, 0]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-3, 1, 0]] 
 ![![43, 0, 0], ![40, 1, 0], ![34, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-3, 1, 0], ![0, -3, 1], ![113, 0, -3]]]
  hmulB := by decide  
  f := ![![![94, -31, 0], ![1333, 0, 0]], ![![88, -29, 0], ![1248, 0, 0]], ![![76, -25, 0], ![1078, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 43, 0], ![-34, 0, 43]], ![![-1, 1, 0], ![2, -3, 1], ![5, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![21, 1, 0]] ![![43, 0, 0], ![-18, 1, 0]]
  ![![43, 0, 0], ![9, 3, 1]] where
 M := ![![![1849, 0, 0], ![-774, 43, 0]], ![![903, 43, 0], ![-378, 3, 1]]]
 hmul := by decide  
 g := ![![![![34, -3, -1], ![43, 0, 0]], ![![-18, 1, 0], ![0, 0, 0]]], ![![![12, -2, -1], ![43, 0, 0]], ![![-9, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![9, 3, 1]] ![![43, 0, 0], ![-3, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-129, 43, 0]], ![![387, 129, 43], ![86, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-3, 1, 0]]], ![![![9, 3, 1]], ![![2, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1026747597, -212375402, -43928334]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-1026747597, -212375402, -43928334]] 
 ![![47, 0, 0], ![0, 47, 0], ![36, 41, 1]] where
  M :=![![![-1026747597, -212375402, -43928334], ![-4963901742, -1026747597, -212375402], ![-23998420426, -4963901742, -1026747597]]]
  hmulB := by decide  
  f := ![![![10125, -7422, 1102]], ![![124526, 10125, -7422]], ![![98540, 5797, -5415]]]
  g := ![![![11801541, 33801836, -43928334], ![57055590, 163417955, -212375402], ![275840278, 790058505, -1026747597]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [33, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 46], [0, 1]]
 g := ![![[14, 21], [40, 7], [13, 12], [31, 17], [1]], ![[41, 26], [2, 40], [15, 35], [26, 30], [1]]]
 h' := ![![[8, 46], [43, 31], [41, 17], [11, 24], [14, 8], [0, 1]], ![[0, 1], [9, 16], [36, 30], [15, 23], [31, 39], [8, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [22, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [33, 39, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1407, 24, 90]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, -78, 90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10125, -7422, 1102]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![10125, -7422, 1102]] 
 ![![47, 0, 0], ![6, 1, 0], ![11, 0, 1]] where
  M :=![![![10125, -7422, 1102], ![124526, 10125, -7422], ![-838686, 124526, 10125]]]
  hmulB := by decide  
  f := ![![![-1026747597, -212375402, -43928334]], ![![-236689092, -48957447, -10126498]], ![![-750907319, -155319812, -32126793]]]
  g := ![![![905, -7422, 1102], ![3094, 10125, -7422], ![-36111, 124526, 10125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-1026747597, -212375402, -43928334]] ![![10125, -7422, 1102]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-6, -10, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-6, -10, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![47, 43, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-6, -10, 1], ![113, -6, -10], ![-1130, 113, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -43, 53]], ![![-1, -1, 1], ![11, 8, -10], ![-16, 7, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [14, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 52], [0, 1]]
 g := ![![[8, 40], [28], [15, 9], [7], [47, 1]], ![[33, 13], [28], [14, 44], [7], [41, 52]]]
 h' := ![![[47, 52], [36, 27], [2, 9], [15, 50], [31, 22], [0, 1]], ![[0, 1], [33, 26], [1, 44], [33, 3], [5, 31], [47, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [48, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [14, 6, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-657, 1025, -23]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, 38, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![10, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![10, 1, 0]] 
 ![![53, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![10, 1, 0], ![0, 10, 1], ![113, 0, 10]]]
  hmulB := by decide  
  f := ![![![141, 14, 0], ![-742, 0, 0]], ![![10, 1, 0], ![-52, 0, 0]], ![![2, 0, 0], ![-10, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 53, 0], ![-6, 0, 53]], ![![0, 1, 0], ![-2, 10, 1], ![1, 0, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-6, -10, 1]] ![![53, 0, 0], ![10, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![530, 53, 0]], ![![-318, -530, 53], ![53, -106, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![10, 1, 0]]], ![![![-6, -10, 1]], ![![1, -2, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19712, 2332, 361]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-19712, 2332, 361]] 
 ![![59, 0, 0], ![0, 59, 0], ![16, 55, 1]] where
  M :=![![![-19712, 2332, 361], ![40793, -19712, 2332], ![263516, 40793, -19712]]]
  hmulB := by decide  
  f := ![![![4973452, 1028723, 212784]], ![![24044592, 4973452, 1028723]], ![![25733449, 5322780, 1100979]]]
  g := ![![![-432, -297, 361], ![59, -2508, 2332], ![9812, 19067, -19712]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [41, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 58], [0, 1]]
 g := ![![[40, 36], [55, 20], [57], [55, 48], [12, 1]], ![[0, 23], [0, 39], [57], [41, 11], [24, 58]]]
 h' := ![![[12, 58], [46, 6], [15, 43], [46, 36], [39, 44], [0, 1]], ![[0, 1], [0, 53], [0, 16], [6, 23], [36, 15], [12, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [23, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [41, 47, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![267, 66, -46]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 44, -46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4973452, -1028723, -212784]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-4973452, -1028723, -212784]] 
 ![![59, 0, 0], ![4, 1, 0], ![43, 0, 1]] where
  M :=![![![-4973452, -1028723, -212784], ![-24044592, -4973452, -1028723], ![-116245699, -24044592, -4973452]]]
  hmulB := by decide  
  f := ![![![19712, -2332, -361]], ![![645, 176, -64]], ![![9900, -2391, 71]]]
  g := ![![![140528, -1028723, -212784], ![679395, -4973452, -1028723], ![3284595, -24044592, -4973452]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-19712, 2332, 361]] ![![-4973452, -1028723, -212784]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![16, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![16, 1, 0]] 
 ![![61, 0, 0], ![16, 1, 0], ![49, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![16, 1, 0], ![0, 16, 1], ![113, 0, 16]]]
  hmulB := by decide  
  f := ![![![417, 26, 0], ![-1586, 0, 0]], ![![112, 7, 0], ![-426, 0, 0]], ![![357, 22, 0], ![-1358, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 61, 0], ![-49, 0, 61]], ![![0, 1, 0], ![-5, 16, 1], ![-11, 0, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![27, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![0, 20, 1], ![113, 0, 20]]]
  hmulB := by decide  
  f := ![![![481, 24, 0], ![-1464, 0, 0]], ![![140, 7, 0], ![-426, 0, 0]], ![![207, 10, 0], ![-630, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-27, 0, 61]], ![![0, 1, 0], ![-7, 20, 1], ![-7, 0, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![25, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![25, 1, 0]] 
 ![![61, 0, 0], ![25, 1, 0], ![46, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![25, 1, 0], ![0, 25, 1], ![113, 0, 25]]]
  hmulB := by decide  
  f := ![![![401, 16, 0], ![-976, 0, 0]], ![![125, 5, 0], ![-304, 0, 0]], ![![286, 11, 0], ![-696, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 61, 0], ![-46, 0, 61]], ![![0, 1, 0], ![-11, 25, 1], ![-17, 0, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![16, 1, 0]] ![![61, 0, 0], ![20, 1, 0]]
  ![![61, 0, 0], ![15, -25, 1]] where
 M := ![![![3721, 0, 0], ![1220, 61, 0]], ![![976, 61, 0], ![320, 36, 1]]]
 hmul := by decide  
 g := ![![![![46, 25, -1], ![61, 0, 0]], ![![5, 26, -1], ![61, 0, 0]]], ![![![1, 26, -1], ![61, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![15, -25, 1]] ![![61, 0, 0], ![25, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1525, 61, 0]], ![![915, -1525, 61], ![488, -610, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![25, 1, 0]]], ![![![15, -25, 1]], ![![8, -10, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [25, 61, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 61, 47], [57, 5, 20], [0, 1]]
 g := ![![[37, 41, 9], [50, 36, 26], [40, 64], [63, 24], [3, 1], []], ![[15, 3, 6, 37], [52, 31, 54, 9], [9, 37], [3, 62], [57, 25], [33, 65]], ![[50, 44, 0, 28], [66, 29, 26, 66], [44, 29], [39, 37], [6, 36], [60, 65]]]
 h' := ![![[13, 61, 47], [23, 20, 64], [34, 13, 19], [30, 24, 8], [59, 60, 15], [0, 0, 1], [0, 1]], ![[57, 5, 20], [40, 6, 54], [0, 62, 36], [52, 56, 29], [44, 15, 14], [14, 25, 5], [13, 61, 47]], ![[0, 1], [3, 41, 16], [37, 59, 12], [47, 54, 30], [33, 59, 38], [7, 42, 61], [57, 5, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 40], []]
 b := ![[], [63, 19, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [25, 61, 64, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1075685, 133598, 30820]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16055, 1994, 460]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-33, 31, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-33, 31, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![38, 31, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-33, 31, 1], ![113, -33, 31], ![3503, 113, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -31, 71]], ![![-1, 0, 1], ![-15, -14, 31], ![67, 16, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [51, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 70], [0, 1]]
 g := ![![[22, 3], [19, 32], [70, 9], [24], [54], [1]], ![[64, 68], [41, 39], [54, 62], [24], [54], [1]]]
 h' := ![![[14, 70], [25, 28], [51, 48], [33, 68], [60, 38], [20, 14], [0, 1]], ![[0, 1], [62, 43], [13, 23], [62, 3], [24, 33], [3, 57], [14, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [16, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [51, 57, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-683, 278, -46]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 24, -46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-31, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-31, 1, 0]] 
 ![![71, 0, 0], ![40, 1, 0], ![33, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-31, 1, 0], ![0, -31, 1], ![113, 0, -31]]]
  hmulB := by decide  
  f := ![![![2016, -65, 0], ![4615, 0, 0]], ![![1148, -37, 0], ![2628, 0, 0]], ![![944, -30, 0], ![2161, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 71, 0], ![-33, 0, 71]], ![![-1, 1, 0], ![17, -31, 1], ![16, 0, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-33, 31, 1]] ![![71, 0, 0], ![-31, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2201, 71, 0]], ![![-2343, 2201, 71], ![1136, -994, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-31, 1, 0]]], ![![![-33, 31, 1]], ![![16, -14, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [8, 52, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12, 31], [69, 60, 42], [0, 1]]
 g := ![![[36, 36, 38], [60, 3], [52, 1], [54, 29, 3], [0, 1], []], ![[43, 23, 64, 68], [10, 2], [71, 27], [61, 5, 5, 34], [21, 23], [14, 12]], ![[57, 47, 19, 42], [7, 35], [12, 8], [18, 19, 50, 45], [25, 71], [3, 12]]]
 h' := ![![[4, 12, 31], [37, 17, 44], [58, 9, 52], [6, 26, 1], [0, 65, 21], [0, 0, 1], [0, 1]], ![[69, 60, 42], [42, 0, 28], [66, 66, 41], [14, 22, 63], [69, 19, 63], [50, 2, 60], [4, 12, 31]], ![[0, 1], [55, 56, 1], [44, 71, 53], [40, 25, 9], [10, 62, 62], [65, 71, 12], [69, 60, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 59], []]
 b := ![[], [43, 69, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [8, 52, 0, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![102273, 730, 1460]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1401, 10, 20]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [45, 77, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 1, 1], [72, 77, 78], [0, 1]]
 g := ![![[12, 10, 11], [64, 47, 36], [63, 47, 10], [11, 73, 22], [6, 1], []], ![[55, 9, 34, 19], [9, 51, 42, 5], [27, 60, 55, 9], [57, 56, 31, 31], [36, 4], [8, 1]], ![[36, 71, 51, 70], [39, 2, 21, 35], [27, 22, 59, 34], [39, 21, 77, 15], [12, 1], [10, 1]]]
 h' := ![![[13, 1, 1], [43, 69, 66], [9, 32, 6], [58, 38, 57], [46, 46, 38], [0, 0, 1], [0, 1]], ![[72, 77, 78], [26, 29, 16], [69, 14, 20], [14, 25, 3], [22, 11, 49], [46, 76, 77], [13, 1, 1]], ![[0, 1], [33, 60, 76], [65, 33, 53], [3, 16, 19], [49, 22, 71], [73, 3, 1], [72, 77, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 6], []]
 b := ![[], [6, 50, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [45, 77, 73, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-367429, 99698, -4898]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4651, 1262, -62]
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



lemma PB167I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB167I1 : PrimesBelowBoundCertificateInterval O 31 79 167 where
  m := 11
  g := ![1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB167I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
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
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
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
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
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
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
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
  β := ![I41N1, I43N0, I43N1, I43N2, I47N1, I53N1, I59N1, I61N0, I61N1, I61N2, I71N1]
  Il := ![[], [I41N1], [I43N0, I43N1, I43N2], [I47N1], [I53N1], [I59N1], [I61N0, I61N1, I61N2], [], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
