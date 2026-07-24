
import IdealArithmetic.Examples.NF3_1_377196_2.RI3_1_377196_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-19, -14, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-19, -14, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![18, 23, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-19, -14, 1], ![104, -11, -97], ![-1634, -94, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -23, 37]], ![![-1, -1, 1], ![50, 60, -97], ![-32, 13, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [28, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 36], [0, 1]]
 g := ![![[31, 4], [4], [8, 4], [30], [1]], ![[0, 33], [4], [14, 33], [30], [1]]]
 h' := ![![[20, 36], [3, 35], [35, 2], [18, 35], [9, 20], [0, 1]], ![[0, 1], [0, 2], [1, 35], [15, 2], [2, 17], [20, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [16, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [28, 17, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2547, 979, 308]
  a := ![-1, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81, -165, 308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![-14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![-14, 1, 0]] 
 ![![37, 0, 0], ![23, 1, 0], ![25, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![-14, 1, 0], ![1, -14, 7], ![118, 8, -13]]]
  hmulB := by decide  
  f := ![![![133, -2433, 1218], ![-111, -6438, 0]], ![![95, -1511, 756], ![-36, -3996, 0]], ![![91, -1644, 823], ![-72, -4350, 0]]]
  g := ![![![1, 0, 0], ![-23, 37, 0], ![-25, 0, 37]], ![![-1, 1, 0], ![4, -14, 7], ![7, 8, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![-19, -14, 1]] ![![37, 0, 0], ![-14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![-518, 37, 0]], ![![-703, -518, 37], ![370, 185, -111]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![-14, 1, 0]]], ![![![-19, -14, 1]], ![![10, 5, -3]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [23, 20, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 32, 2], [8, 8, 39], [0, 1]]
 g := ![![[4, 9, 10], [18, 23], [29, 23], [25, 39, 1], []], ![[7, 25, 19, 31], [5, 18], [6, 2], [20, 4, 9, 5], [38, 4]], ![[10, 37, 4, 5], [17, 4], [28, 10], [10, 26, 31, 2], [1, 4]]]
 h' := ![![[31, 32, 2], [14, 15, 16], [31, 4, 8], [40, 38, 8], [0, 0, 1], [0, 1]], ![[8, 8, 39], [26, 19, 35], [31, 0, 31], [28, 22, 17], [5, 25, 8], [31, 32, 2]], ![[0, 1], [11, 7, 31], [22, 37, 2], [16, 22, 16], [0, 16, 32], [8, 8, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 23], []]
 b := ![[], [37, 38, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [23, 20, 2, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6347743, 912004, 181548]
  a := ![2, -2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![154823, 22244, 4428]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![14, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![14, 1, 0]] 
 ![![43, 0, 0], ![14, 1, 0], ![9, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![14, 1, 0], ![1, 14, 7], ![118, 8, 15]]]
  hmulB := by decide  
  f := ![![![-171, -2798, -1400], ![-86, 8600, 0]], ![![-65, -910, -455], ![1, 2795, 0]], ![![-41, -586, -293], ![-2, 1800, 0]]]
  g := ![![![1, 0, 0], ![-14, 43, 0], ![-9, 0, 43]], ![![0, 1, 0], ![-6, 14, 7], ![-3, 8, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![14, 1, 0]] ![![43, 0, 0], ![14, 1, 0]]
  ![![43, 0, 0], ![-21, 4, 1]] where
 M := ![![![1849, 0, 0], ![602, 43, 0]], ![![602, 43, 0], ![197, 28, 7]]]
 hmul := by decide  
 g := ![![![![43, 0, 0], ![0, 0, 0]], ![![14, 1, 0], ![0, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![7, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-21, 4, 1]] ![![43, 0, 0], ![14, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![602, 43, 0]], ![![-903, 172, 43], ![-172, 43, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![14, 1, 0]]], ![![![-21, 4, 1]], ![![-4, 1, 1]]]]
 hle2 := by decide  

def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59447813, -5318982, 6202902]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-59447813, -5318982, 6202902]] 
 ![![47, 0, 0], ![0, 47, 0], ![3, 41, 1]] where
  M :=![![![-59447813, -5318982, 6202902], ![726623454, -9824597, -31029972], ![-515987640, 69100380, -15143579]]]
  hmulB := by decide  
  f := ![![![48786434412809, 7405839599706, 4808273934234]], ![![574782163839318, 87252625886681, 56649151132176]], ![![524954596260255, 79688741016317, 51738265610815]]]
  g := ![![![-1660777, -5524212, 6202902], ![17440710, 26859665, -31029972], ![-10011849, 14680577, -15143579]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [37, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 46], [0, 1]]
 g := ![![[17, 14], [45, 3], [46, 14], [12, 42], [1]], ![[0, 33], [38, 44], [29, 33], [8, 5], [1]]]
 h' := ![![[29, 46], [27, 25], [37, 35], [26, 22], [10, 29], [0, 1]], ![[0, 1], [0, 22], [18, 12], [6, 25], [5, 18], [29, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [25, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [37, 18, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2662675, 2745490, 1266065]
  a := ![-65, 1, -391]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24160, -1046025, 1266065]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48786434412809, -7405839599706, -4808273934234]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-48786434412809, -7405839599706, -4808273934234]] 
 ![![47, 0, 0], ![41, 1, 0], ![42, 0, 1]] where
  M :=![![![-48786434412809, -7405839599706, -4808273934234], ![-574782163839318, -87252625886681, -56649151132176], ![-960438003581520, -145795647613860, -94658465486387]]]
  hmulB := by decide  
  f := ![![![59447813, 5318982, -6202902]], ![![36398657, 4848997, -4750830]], ![![64102038, 3282912, -5220815]]]
  g := ![![![9719159455595, -7405839599706, -4808273934234], ![114507230746085, -87252625886681, -56649151132176], ![191337002106702, -145795647613860, -94658465486387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-59447813, -5318982, 6202902]] ![![-48786434412809, -7405839599706, -4808273934234]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![13, 10, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![13, 10, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![13, 10, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![13, 10, 1], ![128, 21, 71], ![1198, 98, 31]]]
  hmulB := by decide  
  f := ![![![-12, -10, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -10, 53]], ![![0, 0, 1], ![-15, -13, 71], ![15, -4, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [39, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 52], [0, 1]]
 g := ![![[7, 4], [13], [], [42], [45, 1]], ![[28, 49], [13], [], [42], [37, 52]]]
 h' := ![![[45, 52], [23, 2], [0, 38], [41], [47, 25], [0, 1]], ![[0, 1], [7, 51], [14, 15], [41], [6, 28], [45, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [7, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [39, 8, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![538, 3814, 1717]
  a := ![-2, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-411, -252, 1717]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![22, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![1, -18, 7], ![118, 8, -17]]]
  hmulB := by decide  
  f := ![![![279, -6296, 2450], ![-212, -18550, 0]], ![![196, -4156, 1617], ![-105, -12243, 0]], ![![126, -2614, 1017], ![-58, -7700, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-22, 0, 53]], ![![-1, 1, 0], ![9, -18, 7], ![4, 8, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![13, 10, 1]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![689, 530, 53], ![-106, -159, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-18, 1, 0]]], ![![![13, 10, 1]], ![![-2, -3, 1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18126, 343, -1126]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![18126, 343, -1126]] 
 ![![59, 0, 0], ![0, 59, 0], ![21, 14, 1]] where
  M :=![![![18126, 343, -1126], ![-132525, 9118, 1275], ![20206, -17524, 9461]]]
  hmulB := by decide  
  f := ![![![1840822, 279439, 181427]], ![![21687825, 3292238, 2137500]], ![![6415700, 973911, 632316]]]
  g := ![![![708, 273, -1126], ![-2700, -148, 1275], ![-3025, -2542, 9461]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [15, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 58], [0, 1]]
 g := ![![[40, 4], [38, 51], [51], [37, 27], [49, 1]], ![[0, 55], [0, 8], [51], [3, 32], [39, 58]]]
 h' := ![![[49, 58], [20, 2], [47, 46], [35, 13], [32, 26], [0, 1]], ![[0, 1], [0, 57], [0, 13], [23, 46], [8, 33], [49, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [44, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [15, 10, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2541, 986, 357]
  a := ![-1, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-84, -68, 357]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1840822, -279439, -181427]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-1840822, -279439, -181427]] 
 ![![59, 0, 0], ![19, 1, 0], ![16, 0, 1]] where
  M :=![![![-1840822, -279439, -181427], ![-21687825, -3292238, -2137500], ![-36239488, -5501198, -3571677]]]
  hmulB := by decide  
  f := ![![![-18126, -343, 1126]], ![![-3591, -265, 341]], ![![-5258, 204, 145]]]
  g := ![![![107989, -279439, -181427], ![1272283, -3292238, -2137500], ![2125934, -5501198, -3571677]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![18126, 343, -1126]] ![![-1840822, -279439, -181427]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![23, -28, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![23, -28, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![23, 33, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![23, -28, 1], ![90, 31, -195], ![-3286, -206, 3]]]
  hmulB := by decide  
  f := ![![![-22, 28, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -33, 61]], ![![0, -1, 1], ![75, 106, -195], ![-55, -5, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [4, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 60], [0, 1]]
 g := ![![[17, 46], [36], [17, 48], [57, 12], [54, 1]], ![[0, 15], [36], [47, 13], [34, 49], [47, 60]]]
 h' := ![![[54, 60], [27, 30], [54, 6], [16, 32], [28, 45], [0, 1]], ![[0, 1], [0, 31], [12, 55], [36, 29], [18, 16], [54, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [46, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [4, 7, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61717, 7203, 4516]
  a := ![2, 19, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-691, -2325, 4516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![12, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![12, 1, 0]] 
 ![![61, 0, 0], ![12, 1, 0], ![58, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![12, 1, 0], ![1, 12, 7], ![118, 8, 13]]]
  hmulB := by decide  
  f := ![![![-2239, -28882, -16856], ![-854, 146888, 0]], ![![-449, -5674, -3311], ![-121, 28853, 0]], ![![-2122, -27461, -16027], ![-847, 139664, 0]]]
  g := ![![![1, 0, 0], ![-12, 61, 0], ![-58, 0, 61]], ![![0, 1, 0], ![-9, 12, 7], ![-12, 8, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![23, -28, 1]] ![![61, 0, 0], ![12, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![732, 61, 0]], ![![1403, -1708, 61], ![366, -305, -183]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![12, 1, 0]]], ![![![23, -28, 1]], ![![6, -5, -3]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![27, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![27, 1, 0]] 
 ![![67, 0, 0], ![27, 1, 0], ![30, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![27, 1, 0], ![1, 27, 7], ![118, 8, 28]]]
  hmulB := by decide  
  f := ![![![213, 8636, 2240], ![268, -21440, 0]], ![![74, 3454, 896], ![135, -8576, 0]], ![![99, 3867, 1003], ![111, -9600, 0]]]
  g := ![![![1, 0, 0], ![-27, 67, 0], ![-30, 0, 67]], ![![0, 1, 0], ![-14, 27, 7], ![-14, 8, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-24, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-24, 1, 0]] 
 ![![67, 0, 0], ![43, 1, 0], ![4, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-24, 1, 0], ![1, -24, 7], ![118, 8, -23]]]
  hmulB := by decide  
  f := ![![![821, -25430, 7420], ![-670, -71020, 0]], ![![537, -16314, 4760], ![-401, -45560, 0]], ![![68, -1519, 443], ![13, -4240, 0]]]
  g := ![![![1, 0, 0], ![-43, 67, 0], ![-4, 0, 67]], ![![-1, 1, 0], ![15, -24, 7], ![-2, 8, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-4, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-4, 1, 0]] 
 ![![67, 0, 0], ![63, 1, 0], ![17, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-4, 1, 0], ![1, -4, 7], ![118, 8, -3]]]
  hmulB := by decide  
  f := ![![![-1783, 7196, -12600], ![268, 120600, 0]], ![![-1679, 6765, -11844], ![202, 113364, 0]], ![![-453, 1826, -3197], ![58, 30600, 0]]]
  g := ![![![1, 0, 0], ![-63, 67, 0], ![-17, 0, 67]], ![![-1, 1, 0], ![2, -4, 7], ![-5, 8, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![27, 1, 0]] ![![67, 0, 0], ![-24, 1, 0]]
  ![![67, 0, 0], ![-35, 10, 1]] where
 M := ![![![4489, 0, 0], ![-1608, 67, 0]], ![![1809, 67, 0], ![-647, 3, 7]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![11, -9, -1], ![67, 0, 0]]], ![![![27, 1, 0], ![0, 0, 0]], ![![-6, -1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-35, 10, 1]] ![![67, 0, 0], ![-4, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-268, 67, 0]], ![![-2345, 670, 67], ![268, -67, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-4, 1, 0]]], ![![![-35, 10, 1]], ![![4, -1, 1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [31, 70, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 67, 44], [63, 3, 27], [0, 1]]
 g := ![![[18, 66, 8], [46, 65, 9], [17, 45, 15], [44, 25], [2, 1], []], ![[25, 6, 43, 11], [60, 8, 9, 23], [62, 8, 46, 61], [2, 5], [13, 9], [41, 19]], ![[32, 11, 47, 54], [9, 49, 43, 4], [69, 22, 32, 4], [45, 58], [49, 16], [58, 19]]]
 h' := ![![[10, 67, 44], [65, 67, 47], [41, 67, 3], [66, 25, 50], [9, 42, 5], [0, 0, 1], [0, 1]], ![[63, 3, 27], [13, 36, 36], [38, 49, 46], [57, 24, 43], [41, 29, 17], [36, 11, 3], [10, 67, 44]], ![[0, 1], [36, 39, 59], [54, 26, 22], [70, 22, 49], [20, 0, 49], [41, 60, 67], [63, 3, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 9], []]
 b := ![[], [26, 9, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [31, 70, 69, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3928998, -398949, 51049]
  a := ![-2, 3, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55338, -5619, 719]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![16, -5, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![16, -5, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![16, 68, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![16, -5, 1], ![113, 24, -34], ![-572, -22, 19]]]
  hmulB := by decide  
  f := ![![![-15, 5, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -68, 73]], ![![0, -1, 1], ![9, 32, -34], ![-12, -18, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [6, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 72], [0, 1]]
 g := ![![[37, 61], [32], [36], [17, 8], [9], [1]], ![[0, 12], [32], [36], [66, 65], [9], [1]]]
 h' := ![![[70, 72], [29, 34], [41, 55], [44, 6], [55, 9], [67, 70], [0, 1]], ![[0, 1], [0, 39], [22, 18], [26, 67], [28, 64], [3, 3], [70, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [44, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [6, 3, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6849, 3759, 1701]
  a := ![2, 1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-279, -1533, 1701]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![34, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![34, 1, 0]] 
 ![![73, 0, 0], ![34, 1, 0], ![54, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![34, 1, 0], ![1, 34, 7], ![118, 8, 35]]]
  hmulB := by decide  
  f := ![![![-2631, -137998, -28420], ![-3066, 296380, 0]], ![![-1244, -64241, -13230], ![-1386, 137970, 0]], ![![-1956, -102081, -21023], ![-2247, 219240, 0]]]
  g := ![![![1, 0, 0], ![-34, 73, 0], ![-54, 0, 73]], ![![0, 1, 0], ![-21, 34, 7], ![-28, 8, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![16, -5, 1]] ![![73, 0, 0], ![34, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![2482, 73, 0]], ![![1168, -365, 73], ![657, -146, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![34, 1, 0]]], ![![![16, -5, 1]], ![![9, -2, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![2, 15, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![2, 15, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![2, 15, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![2, 15, 1], ![133, 10, 106], ![1788, 138, 25]]]
  hmulB := by decide  
  f := ![![![-1, -15, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -15, 79]], ![![0, 0, 1], ![-1, -20, 106], ![22, -3, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [40, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 78], [0, 1]]
 g := ![![[33, 2], [60, 18], [57, 25], [7, 10], [55], [1]], ![[0, 77], [0, 61], [0, 54], [0, 69], [55], [1]]]
 h' := ![![[23, 78], [49, 70], [11, 27], [36, 74], [32, 57], [39, 23], [0, 1]], ![[0, 1], [0, 9], [0, 52], [0, 5], [0, 22], [15, 56], [23, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [69, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [40, 56, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15985, 16200, 5820]
  a := ![-5, 0, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, -900, 5820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-27, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-27, 1, 0]] 
 ![![79, 0, 0], ![52, 1, 0], ![54, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-27, 1, 0], ![1, -27, 7], ![118, 8, -26]]]
  hmulB := by decide  
  f := ![![![-1842, 63593, -16492], ![1501, 186124, 0]], ![![-1225, 41838, -10850], ![949, 122450, 0]], ![![-1269, 43469, -11273], ![997, 127224, 0]]]
  g := ![![![1, 0, 0], ![-52, 79, 0], ![-54, 0, 79]], ![![-1, 1, 0], ![13, -27, 7], ![14, 8, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![2, 15, 1]] ![![79, 0, 0], ![-27, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2133, 79, 0]], ![![158, 1185, 79], ![79, -395, 79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-27, 1, 0]]], ![![![2, 15, 1]], ![![1, -5, 1]]]]
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


lemma PB174I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB174I1 : PrimesBelowBoundCertificateInterval O 31 79 174 where
  m := 11
  g := ![2, 1, 3, 2, 2, 2, 2, 3, 1, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB174I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
    · exact ![I73N0, I73N1]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
    · exact ![5329, 73]
    · exact ![6241, 79]
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
      exact NI43N0
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
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N0, I47N1, I53N1, I59N1, I61N1, I67N0, I67N1, I67N2, I73N1, I79N1]
  Il := ![[I37N1], [], [I43N0, I43N0, I43N0], [I47N1], [I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N2], [], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
