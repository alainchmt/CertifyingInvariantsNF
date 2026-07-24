
import IdealArithmetic.Examples.NF3_1_504175_1.RI3_1_504175_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5294293, 1601067, 123584]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![5294293, 1601067, 123584]] 
 ![![37, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![5294293, 1601067, 123584], ![68589120, 20742293, 1601067], ![888592185, 268722495, 20742293]]]
  hmulB := by decide  
  f := ![![![-4316, -4551, 377]], ![![5655, 1157, -123]], ![![-68265, -9720, 1157]]]
  g := ![![![143089, 1601067, 123584], ![1853760, 20742293, 1601067], ![24016005, 268722495, 20742293]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4316, -4551, 377]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-4316, -4551, 377]] 
 ![![37, 0, 0], ![0, 37, 0], ![23, 0, 1]] where
  M :=![![![-4316, -4551, 377], ![209235, 42809, -4551], ![-2525805, -359640, 42809]]]
  hmulB := by decide  
  f := ![![![5294293, 1601067, 123584]], ![![68589120, 20742293, 1601067]], ![![27307052, 8258028, 637425]]]
  g := ![![![-351, -123, 377], ![8484, 1157, -4551], ![-94876, -9720, 42809]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [34, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 36], [0, 1]]
 g := ![![[3, 12], [11], [18, 36], [7], [1]], ![[0, 25], [11], [9, 1], [7], [1]]]
 h' := ![![[9, 36], [26, 30], [17, 23], [30, 6], [3, 9], [0, 1]], ![[0, 1], [0, 7], [2, 14], [10, 31], [10, 28], [9, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [18, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [34, 28, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1144, 777, 98]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, 21, 98]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![5294293, 1601067, 123584]] ![![-4316, -4551, 377]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [13, 34, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 16, 30], [20, 24, 11], [0, 1]]
 g := ![![[4, 29, 1], [33, 9], [31, 33], [6, 9, 1], []], ![[9, 22, 12, 29], [17, 16], [], [36, 31, 14, 19], [40, 39]], ![[13, 31, 16, 17], [24, 1], [37, 33], [39, 22, 38, 28], [18, 39]]]
 h' := ![![[30, 16, 30], [18, 31, 40], [23, 8, 38], [4, 7, 22], [0, 0, 1], [0, 1]], ![[20, 24, 11], [35, 9, 4], [25, 20, 4], [5, 2], [11, 36, 24], [30, 16, 30]], ![[0, 1], [21, 1, 38], [13, 13, 40], [24, 32, 19], [2, 5, 16], [20, 24, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 15], []]
 b := ![[], [29, 31, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [13, 34, 32, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4372855, 3022889, 429065]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![106655, 73729, 10465]
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


def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![108087482, 15753655, -1859994]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![108087482, 15753655, -1859994]] 
 ![![43, 0, 0], ![23, 1, 0], ![30, 0, 1]] where
  M :=![![![108087482, 15753655, -1859994], ![-1032296670, -124411768, 15753655], ![8743278525, 936910205, -124411768]]]
  hmulB := by decide  
  f := ![![![718527881336549, 217292711173270, 16772503849633]], ![![600811183890394, 181693563244788, 14024658132903]], ![![3305890491657240, 999746741125655, 77168976233248]]]
  g := ![![![-4615041, 15753655, -1859994], ![31548008, -124411768, 15753655], ![-211007050, 936910205, -124411768]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99218, -8717, 1264]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-99218, -8717, 1264]] 
 ![![43, 0, 0], ![40, 1, 0], ![34, 0, 1]] where
  M :=![![![-99218, -8717, 1264], ![701520, 58782, -8717], ![-4837935, -388105, 58782]]]
  hmulB := by decide  
  f := ![![![72212239, 21837974, 1685641]], ![![88930705, 26893868, 2075898]], ![![338960272, 102506247, 7912306]]]
  g := ![![![4802, -8717, 1264], ![-31474, 58782, -8717], ![202039, -388105, 58782]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![108087482, 15753655, -1859994]] ![![108087482, 15753655, -1859994]]
  ![![-20841987428557376, -1999814529604100, 278540719873309]] where
 M := ![![![-20841987428557376, -1999814529604100, 278540719873309]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![-20841987428557376, -1999814529604100, 278540719873309]] ![![-99218, -8717, 1264]]
  ![![43, 0, 0]] where
 M := ![![![-682571477721539676947, -43976539350884149053, 7461291740455266074]]]
 hmul := by decide  
 g := ![![![![-15873755295849759929, -1022710217462422071, 173518412568727118]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1062489344, 321311387, 24801552]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1062489344, 321311387, 24801552]] 
 ![![47, 0, 0], ![0, 47, 0], ![34, 26, 1]] where
  M :=![![![1062489344, 321311387, 24801552], ![13764861360, 4162683344, 321311387], ![178327819785, 53928784735, 4162683344]]]
  hmulB := by decide  
  f := ![![![-260747, -11264, 2423]], ![![1344765, 42128, -11264]], ![![422276, 13811, -3582]]]
  g := ![![![4664608, -6883595, 24801552], ![60431366, -89178994, 321311387], ![782906087, -1155340047, 4162683344]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [28, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 46], [0, 1]]
 g := ![![[44, 42], [7, 2], [34, 28], [30, 6], [1]], ![[0, 5], [34, 45], [36, 19], [17, 41], [1]]]
 h' := ![![[37, 46], [39, 18], [35, 40], [6, 34], [19, 37], [0, 1]], ![[0, 1], [0, 29], [11, 7], [42, 13], [25, 10], [37, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [40, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [28, 10, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2374, 187, 244]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-126, -131, 244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![260747, 11264, -2423]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![260747, 11264, -2423]] 
 ![![47, 0, 0], ![21, 1, 0], ![29, 0, 1]] where
  M :=![![![260747, 11264, -2423], ![-1344765, -42128, 11264], ![6251520, 63235, -42128]]]
  hmulB := by decide  
  f := ![![![-1062489344, -321311387, -24801552]], ![![-767598672, -232132393, -17917957]], ![![-4449787463, -1345676914, -103870816]]]
  g := ![![![2010, 11264, -2423], ![-16739, -42128, 11264], ![130751, 63235, -42128]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1062489344, 321311387, 24801552]] ![![260747, 11264, -2423]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106414, 32181, 2484]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![106414, 32181, 2484]] 
 ![![53, 0, 0], ![0, 53, 0], ![9, 44, 1]] where
  M :=![![![106414, 32181, 2484], ![1378620, 416914, 32181], ![17860455, 5401245, 416914]]]
  hmulB := by decide  
  f := ![![![-3433, -318, 45]], ![![24975, 2192, -318]], ![![16821, 1487, -215]]]
  g := ![![![1586, -1455, 2484], ![20547, -18850, 32181], ![266193, -244207, 416914]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [51, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 52], [0, 1]]
 g := ![![[17, 24], [49], [49, 42], [11], [34, 1]], ![[38, 29], [49], [46, 11], [11], [15, 52]]]
 h' := ![![[34, 52], [3, 17], [45, 7], [35, 28], [15, 45], [0, 1]], ![[0, 1], [51, 36], [18, 46], [33, 25], [8, 8], [34, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [36, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [51, 19, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3259, 4266, 1063]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-242, -802, 1063]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3433, -318, 45]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-3433, -318, 45]] 
 ![![53, 0, 0], ![9, 1, 0], ![25, 0, 1]] where
  M :=![![![-3433, -318, 45], ![24975, 2192, -318], ![-176490, -14775, 2192]]]
  hmulB := by decide  
  f := ![![![106414, 32181, 2484]], ![![44082, 13331, 1029]], ![![387185, 117090, 9038]]]
  g := ![![![-32, -318, 45], ![249, 2192, -318], ![-1855, -14775, 2192]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![106414, 32181, 2484]] ![![-3433, -318, 45]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22276618639, -2203520149, 302812087]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-22276618639, -2203520149, 302812087]] 
 ![![59, 0, 0], ![0, 59, 0], ![14, 27, 1]] where
  M :=![![![-22276618639, -2203520149, 302812087], ![168060708285, 15574892236, -2203520149], ![-1222953682695, -107379310340, 15574892236]]]
  hmulB := by decide  
  f := ![![![101098207510153204, 30573488065314976, 2359922445181791]], ![![1309756957075894005, 396088513157877079, 30573488065314976]], ![![910967773261713469, 275489180566395878, 21264603477185195]]]
  g := ![![![-449423523, -175922822, 302812087], ![3371355769, 1272371801, -2203520149], ![-24423765661, -8947481368, 15574892236]]]
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
  c := ![1119, 780, 101]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -33, 101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101098207510153204, -30573488065314976, -2359922445181791]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-101098207510153204, -30573488065314976, -2359922445181791]] 
 ![![59, 0, 0], ![32, 1, 0], ![38, 0, 1]] where
  M :=![![![-101098207510153204, -30573488065314976, -2359922445181791], ![-1309756957075894005, -396088513157877079, -30573488065314976], ![-16968285876249811680, -5131442965240266005, -396088513157877079]]]
  hmulB := by decide  
  f := ![![![22276618639, 2203520149, -302812087]], ![![9233747257, 931148348, -126889265]], ![![35075681203, 3239204678, -459012738]]]
  g := ![![![16388651923675154, -30573488065314976, -2359922445181791], ![212319796787426129, -396088513157877079, -30573488065314976], ![2750665296804034398, -5131442965240266005, -396088513157877079]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-22276618639, -2203520149, 302812087]] ![![-101098207510153204, -30573488065314976, -2359922445181791]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![198748721, 13507468, -2226780]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![198748721, 13507468, -2226780]] 
 ![![61, 0, 0], ![0, 61, 0], ![36, 51, 1]] where
  M :=![![![198748721, 13507468, -2226780], ![-1235862900, -79598779, 13507468], ![7496644740, 452570600, -79598779]]]
  hmulB := by decide  
  f := ![![![3653815099181, 1104963926452, 85290535564]], ![![47336247238020, 14315132044681, 1104963926452]], ![![51785916916236, 15660773338943, 1208831993017]]]
  g := ![![![4572341, 2083168, -2226780], ![-28231668, -12598027, 13507468], ![169872144, 73968989, -79598779]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [1, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 60], [0, 1]]
 g := ![![[24, 1], [36], [45, 58], [30, 5], [37, 1]], ![[0, 60], [36], [56, 3], [32, 56], [13, 60]]]
 h' := ![![[37, 60], [37, 60], [16, 6], [31, 34], [24, 26], [0, 1]], ![[0, 1], [0, 1], [55, 55], [8, 27], [10, 35], [37, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [52, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [1, 24, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21116, 5799, 512]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, -333, 512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3653815099181, 1104963926452, 85290535564]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![3653815099181, 1104963926452, 85290535564]] 
 ![![61, 0, 0], ![10, 1, 0], ![22, 0, 1]] where
  M :=![![![3653815099181, 1104963926452, 85290535564], ![47336247238020, 14315132044681, 1104963926452], ![613254979180860, 185456738044520, 14315132044681]]]
  hmulB := by decide  
  f := ![![![198748721, 13507468, -2226780]], ![![12321710, 909441, -143612]], ![![194575682, 12290736, -2107999]]]
  g := ![![![-152003540127, 1104963926452, 85290535564], ![-1969250485094, 14315132044681, 1104963926452], ![-25512218135202, 185456738044520, 14315132044681]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![198748721, 13507468, -2226780]] ![![3653815099181, 1104963926452, 85290535564]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![8, 1, 0]] 
 ![![67, 0, 0], ![8, 1, 0], ![3, 0, 1]] where
  M :=![![![8, 1, 0], ![0, 8, 1], ![555, 125, 8]]]
  hmulB := by decide  
  f := ![![![-61, -8, 1]], ![![1, 0, 0]], ![![-69, -7, 1]]]
  g := ![![![0, 1, 0], ![-1, 8, 1], ![-7, 125, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -7, 1]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-77, -7, 1]] 
 ![![67, 0, 0], ![51, 1, 0], ![12, 0, 1]] where
  M :=![![![-77, -7, 1], ![555, 48, -7], ![-3885, -320, 48]]]
  hmulB := by decide  
  f := ![![![64, 16, 1]], ![![57, 15, 1]], ![![144, 41, 3]]]
  g := ![![![4, -7, 1], ![-27, 48, -7], ![177, -320, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![8, 1, 0]] ![![8, 1, 0]]
  ![![64, 16, 1]] where
 M := ![![![64, 16, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI67N1 : IdealMulLeCertificate' Table 
  ![![64, 16, 1]] ![![-77, -7, 1]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52596311296, -4067066526, 627303285]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-52596311296, -4067066526, 627303285]] 
 ![![71, 0, 0], ![0, 71, 0], ![47, 39, 1]] where
  M :=![![![-52596311296, -4067066526, 627303285], ![348153323175, 25816599329, -4067066526], ![-2257221921930, -160229992575, 25816599329]]]
  hmulB := by decide  
  f := ![![![-208883966917073321, -63169383778969749, -4875951553510041]], ![![-2706153112198072755, -818377911105828446, -63169383778969749]], ![![-2118542617157119637, -640676417680396887, -49452867626769304]]]
  g := ![![![-1156050221, -401857671, 627303285], ![7595851407, 2597636533, -4067066526], ![-48881719583, -16437709386, 25816599329]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [20, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 70], [0, 1]]
 g := ![![[56, 32], [61, 45], [16, 5], [32], [43], [1]], ![[0, 39], [0, 26], [25, 66], [32], [43], [1]]]
 h' := ![![[16, 70], [58, 23], [35, 20], [19, 17], [37, 48], [51, 16], [0, 1]], ![[0, 1], [0, 48], [0, 51], [7, 54], [24, 23], [23, 55], [16, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [13, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [20, 55, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3364, -36, 81]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-101, -45, 81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38947597196, 5076223353, -623878640]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![38947597196, 5076223353, -623878640]] 
 ![![71, 0, 0], ![32, 1, 0], ![41, 0, 1]] where
  M :=![![![38947597196, 5076223353, -623878640], ![-346252645200, -39037232804, 5076223353], ![2817303960915, 288275273925, -39037232804]]]
  hmulB := by decide  
  f := ![![![60555867403136731891, 18312926954206009812, 1413547818419656049]], ![![38342349241173021517, 11595253623101212000, 895020523149788780]], ![![178119225677647062721, 53865703008747982197, 4157814158602811775]]]
  g := ![![![-1379049660, 5076223353, -623878640], ![9786107705, -39037232804, 5076223353], ![-67703919151, 288275273925, -39037232804]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-52596311296, -4067066526, 627303285]] ![![38947597196, 5076223353, -623878640]]
  ![![71, 0, 0]] where
 M := ![![![1127036626005332954959, 72612425439831967041, -12319807292379625378]]]
 hmul := by decide  
 g := ![![![![15873755295849759929, 1022710217462422071, -173518412568727118]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103, -5, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-103, -5, 1]] 
 ![![73, 0, 0], ![11, 1, 0], ![25, 0, 1]] where
  M :=![![![-103, -5, 1], ![555, 22, -5], ![-2775, -70, 22]]]
  hmulB := by decide  
  f := ![![![134, 40, 3]], ![![43, 13, 1]], ![![350, 105, 8]]]
  g := ![![![-1, -5, 1], ![6, 22, -5], ![-35, -70, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17898703, -1658170, 21350]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![17898703, -1658170, 21350]] 
 ![![73, 0, 0], ![27, 1, 0], ![1, 0, 1]] where
  M :=![![![17898703, -1658170, 21350], ![11849250, 20567453, -1658170], ![-920284350, -195422000, 20567453]]]
  hmulB := by decide  
  f := ![![![-98977225167209, -29932073841010, -2310412627350]], ![![-54173480653341, -16382805442373, -1264564586020]], ![![-228921619272983, -69229045371870, -5343687893333]]]
  g := ![![![858191, -1658170, 21350], ![-7422107, 20567453, -1658170], ![59390989, -195422000, 20567453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1567000156778872, -473882393877400, -36578282965249]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![-1567000156778872, -473882393877400, -36578282965249]] 
 ![![73, 0, 0], ![35, 1, 0], ![16, 0, 1]] where
  M :=![![![-1567000156778872, -473882393877400, -36578282965249], ![-20300947045713195, -6139285527434997, -473882393877400], ![-263004728601957000, -79536246280388195, -6139285527434997]]]
  hmulB := by decide  
  f := ![![![-2823097009, -127467755, 26659253]], ![![-1150856300, -54137833, 11035700]], ![![-1587865153, -43521480, 12819968]]]
  g := ![![![213755289813344, -473882393877400, -36578282965249], ![2769262530363700, -6139285527434997, -473882393877400], ![35876609036309449, -79536246280388195, -6139285527434997]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-103, -5, 1]] ![![17898703, -1658170, 21350]]
  ![![-2823097009, -127467755, 26659253]] where
 M := ![![![-2823097009, -127467755, 26659253]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-2823097009, -127467755, 26659253]] ![![-1567000156778872, -473882393877400, -36578282965249]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10146190661, 382102214, -89945604]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![10146190661, 382102214, -89945604]] 
 ![![79, 0, 0], ![0, 79, 0], ![43, 57, 1]] where
  M :=![![![10146190661, 382102214, -89945604], ![-49919810220, -1097009839, 382102214], ![212066728770, -2157033470, -1097009839]]]
  hmulB := by decide  
  f := ![![![25666301916733019, 7761842614798094, 599125182036760]], ![![332514476030401800, 100556949671328019, 7761842614798094]], ![![308415174270447653, 93268989450407325, 7199295715726583]]]
  g := ![![![177390527, 69734198, -89945604], ![-839876018, -289580203, 382102214], ![3281495593, 764209207, -1097009839]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [9, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 78], [0, 1]]
 g := ![![[32, 44], [42, 38], [26, 16], [30, 20], [73], [1]], ![[0, 35], [0, 41], [0, 63], [37, 59], [73], [1]]]
 h' := ![![[28, 78], [17, 53], [3, 14], [46, 4], [56, 39], [70, 28], [0, 1]], ![[0, 1], [0, 26], [0, 65], [0, 75], [42, 40], [64, 51], [28, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [52, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [9, 51, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2229, 2771, 603]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-300, -400, 603]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25666301916733019, 7761842614798094, 599125182036760]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![25666301916733019, 7761842614798094, 599125182036760]] 
 ![![79, 0, 0], ![22, 1, 0], ![69, 0, 1]] where
  M :=![![![25666301916733019, 7761842614798094, 599125182036760], ![332514476030401800, 100556949671328019, 7761842614798094], ![4307822651212942170, 1302744802880163550, 100556949671328019]]]
  hmulB := by decide  
  f := ![![![10146190661, 382102214, -89945604]], ![![2193625118, 92522011, -20211406]], ![![11546251701, 306430624, -92446285]]]
  g := ![![![-2359922445181791, 7761842614798094, 599125182036760], ![-30573488065314976, 100556949671328019, 7761842614798094], ![-396088513157877079, 1302744802880163550, 100556949671328019]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![10146190661, 382102214, -89945604]] ![![25666301916733019, 7761842614798094, 599125182036760]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB201I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB201I1 : PrimesBelowBoundCertificateInterval O 31 79 201 where
  m := 11
  g := ![2, 1, 3, 2, 2, 2, 2, 3, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB201I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![37, 1369]
    · exact ![68921]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
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
      exact NI43N1
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
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I43N0, I43N1, I47N1, I53N1, I59N1, I61N1, I67N0, I67N1, I71N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N0], [], [I43N0, I43N0, I43N1], [I47N1], [I53N1], [I59N1], [I61N1], [I67N0, I67N0, I67N1], [I71N1], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
