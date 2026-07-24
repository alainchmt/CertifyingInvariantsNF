
import IdealArithmetic.Examples.NF3_3_787077_1.RI3_3_787077_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29124, -17346, -7099]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-29124, -17346, -7099]] 
 ![![37, 0, 0], ![0, 37, 0], ![36, 31, 1]] where
  M :=![![![-29124, -17346, -7099], ![-481929, -287033, -117471], ![-808838, -481737, -197155]]]
  hmulB := by decide  
  f := ![![![-3676, 9, 127]], ![![8019, 34, -309]], ![![3020, 34, -129]]]
  g := ![![![6120, 5479, -7099], ![101271, 90664, -117471], ![169966, 152164, -197155]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [25, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 36], [0, 1]]
 g := ![![[31, 3], [12], [26, 28], [4], [1]], ![[0, 34], [12], [8, 9], [4], [1]]]
 h' := ![![[2, 36], [30, 22], [16, 30], [7, 19], [12, 2], [0, 1]], ![[0, 1], [0, 15], [2, 7], [8, 18], [16, 35], [2, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [10, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [25, 35, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1779, 2978, 3956]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3801, -3234, 3956]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3676, -9, -127]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![3676, -9, -127]] 
 ![![37, 0, 0], ![14, 1, 0], ![26, 0, 1]] where
  M :=![![![3676, -9, -127], ![-8019, -34, 309], ![4513, 120, -234]]]
  hmulB := by decide  
  f := ![![![29124, 17346, 7099]], ![![24045, 14321, 5861]], ![![42326, 25209, 10317]]]
  g := ![![![192, -9, -127], ![-421, -34, 309], ![241, 120, -234]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-29124, -17346, -7099]] ![![3676, -9, -127]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17718, 6037, -4235]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![17718, 6037, -4235]] 
 ![![41, 0, 0], ![18, 1, 0], ![35, 0, 1]] where
  M :=![![![17718, 6037, -4235], ![-254731, -86986, 61001], ![549731, 187778, -131678]]]
  hmulB := by decide  
  f := ![![![-503270, -299744, -122673]], ![![-424067, -252571, -103367]], ![![-770522, -458917, -187816]]]
  g := ![![![1397, 6037, -4235], ![-20098, -86986, 61001], ![43377, 187778, -131678]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![455, -4, -14]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![455, -4, -14]] 
 ![![41, 0, 0], ![32, 1, 0], ![14, 0, 1]] where
  M :=![![![455, -4, -14], ![-890, 37, 10], ![308, -74, 33]]]
  hmulB := by decide  
  f := ![![![-1961, -1168, -478]], ![![-2322, -1383, -566]], ![![-1998, -1190, -487]]]
  g := ![![![19, -4, -14], ![-54, 37, 10], ![54, -74, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![17718, 6037, -4235]] ![![455, -4, -14]]
  ![![1384380, 465887, -327437]] where
 M := ![![![1384380, 465887, -327437]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![1384380, 465887, -327437]] ![![455, -4, -14]]
  ![![41, 0, 0]] where
 M := ![![![114402874, 35930637, -25527871]]]
 hmul := by decide  
 g := ![![![![2790314, 876357, -622631]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12545, -7472, -3058]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-12545, -7472, -3058]] 
 ![![43, 0, 0], ![0, 43, 0], ![15, 41, 1]] where
  M :=![![![-12545, -7472, -3058], ![-207598, -123643, -50602], ![-348416, -207514, -84927]]]
  hmulB := by decide  
  f := ![![![-131, -76, 50]], ![![2998, 1091, -758]], ![![2655, 959, -667]]]
  g := ![![![775, 2742, -3058], ![12824, 45373, -50602], ![21523, 76151, -84927]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [30, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 42], [0, 1]]
 g := ![![[22, 40], [11, 13], [24], [19, 10], [1]], ![[24, 3], [31, 30], [24], [41, 33], [1]]]
 h' := ![![[28, 42], [14, 13], [3, 20], [32, 14], [13, 28], [0, 1]], ![[0, 1], [34, 30], [4, 23], [37, 29], [23, 15], [28, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [6, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [30, 15, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-900, 851, 2606]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-930, -2465, 2606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 76, -50]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![131, 76, -50]] 
 ![![43, 0, 0], ![19, 1, 0], ![34, 0, 1]] where
  M :=![![![131, 76, -50], ![-2998, -1091, 758], ![6788, 2354, -1647]]]
  hmulB := by decide  
  f := ![![![12545, 7472, 3058]], ![![10371, 6177, 2528]], ![![18022, 10734, 4393]]]
  g := ![![![9, 76, -50], ![-187, -1091, 758], ![420, 2354, -1647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-12545, -7472, -3058]] ![![131, 76, -50]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18118, 197, 535]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-18118, 197, 535]] 
 ![![47, 0, 0], ![0, 47, 0], ![17, 24, 1]] where
  M :=![![![-18118, 197, 535], ![34099, -2012, -29], ![-8989, 4108, -2124]]]
  hmulB := by decide  
  f := ![![![93460, 55664, 22781]], ![![1546531, 921101, 376969]], ![![878748, 523375, 214196]]]
  g := ![![![-579, -269, 535], ![736, -28, -29], ![577, 1172, -2124]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [14, 10, 1] where
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
 g := ![![[41, 37], [4, 18], [8, 24], [32, 6], [1]], ![[0, 10], [12, 29], [3, 23], [19, 41], [1]]]
 h' := ![![[37, 46], [38, 32], [29, 21], [22, 27], [33, 37], [0, 1]], ![[0, 1], [0, 15], [7, 26], [34, 20], [39, 10], [37, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [19, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [14, 10, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2909439, 4606387, 6220096]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2187919, -3078211, 6220096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93460, 55664, 22781]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![93460, 55664, 22781]] 
 ![![47, 0, 0], ![46, 1, 0], ![24, 0, 1]] where
  M :=![![![93460, 55664, 22781], ![1546531, 921101, 376969], ![2595592, 1545913, 632679]]]
  hmulB := by decide  
  f := ![![![-18118, 197, 535]], ![![-17007, 150, 523]], ![![-9443, 188, 228]]]
  g := ![![![-64124, 55664, 22781], ![-1061093, 921101, 376969], ![-1780866, 1545913, 632679]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-18118, 197, 535]] ![![93460, 55664, 22781]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14360, 255, -669]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![14360, 255, -669]] 
 ![![53, 0, 0], ![0, 53, 0], ![29, 26, 1]] where
  M :=![![![14360, 255, -669], ![-41637, -4276, 4047], ![42825, 9402, -7144]]]
  hmulB := by decide  
  f := ![![![141550, 84306, 34503]], ![![2342301, 1395055, 570939]], ![![1300678, 774673, 317042]]]
  g := ![![![637, 333, -669], ![-3000, -2066, 4047], ![4717, 3682, -7144]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [24, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 52], [0, 1]]
 g := ![![[26, 42], [4], [2, 38], [37], [12, 1]], ![[0, 11], [4], [34, 15], [37], [24, 52]]]
 h' := ![![[12, 52], [35, 28], [5, 51], [12, 12], [30, 14], [0, 1]], ![[0, 1], [0, 25], [34, 2], [50, 41], [39, 39], [12, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [40, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [24, 41, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-266, 2417, 4600]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2522, -2211, 4600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![141550, 84306, 34503]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![141550, 84306, 34503]] 
 ![![53, 0, 0], ![7, 1, 0], ![18, 0, 1]] where
  M :=![![![141550, 84306, 34503], ![2342301, 1395055, 570939], ![3931158, 2341365, 958225]]]
  hmulB := by decide  
  f := ![![![14360, 255, -669]], ![![1111, -47, -12]], ![![5685, 264, -362]]]
  g := ![![![-20182, 84306, 34503], ![-333962, 1395055, 570939], ![-560499, 2341365, 958225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![14360, 255, -669]] ![![141550, 84306, 34503]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [36, 23, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 10, 54], [5, 48, 5], [0, 1]]
 g := ![![[4, 28, 53], [25, 13, 20], [33, 51], [8, 24, 28], [1]], ![[14, 52, 49, 56], [57, 4, 24, 6], [1, 45], [44, 8, 44, 34], [6, 58, 12, 52]], ![[27, 46, 19, 15], [48, 38, 12, 49], [20, 3], [47, 44, 33, 16], [38, 21, 31, 7]]]
 h' := ![![[33, 10, 54], [44, 48, 42], [41, 51, 43], [7, 12, 46], [23, 36, 38], [0, 1]], ![[5, 48, 5], [45, 20, 6], [12, 25, 39], [15, 32, 24], [26, 0, 51], [33, 10, 54]], ![[0, 1], [49, 50, 11], [54, 42, 36], [40, 15, 48], [55, 23, 29], [5, 48, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 58], []]
 b := ![[], [13, 40, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [36, 23, 21, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1659729, -1574179, -1518660]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28131, -26681, -25740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, -8, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-18, -8, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![43, 53, 1]] where
  M :=![![![-18, -8, 1], ![47, -13, -67], ![-544, -235, 37]]]
  hmulB := by decide  
  f := ![![![266, -1, -9]], ![![-569, 2, 19]], ![![-302, 1, 10]]]
  g := ![![![-1, -1, 1], ![48, 58, -67], ![-35, -36, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [48, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 60], [0, 1]]
 g := ![![[30, 14], [1], [10, 56], [42, 14], [24, 1]], ![[0, 47], [1], [12, 5], [12, 47], [48, 60]]]
 h' := ![![[24, 60], [16, 40], [8, 1], [58, 19], [7, 40], [0, 1]], ![[0, 1], [0, 21], [32, 60], [26, 42], [52, 21], [24, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [42, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [48, 37, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![178564, 216849, 255728]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177340, -218635, 255728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![266, -1, -9]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![266, -1, -9]] 
 ![![61, 0, 0], ![6, 1, 0], ![24, 0, 1]] where
  M :=![![![266, -1, -9], ![-569, 2, 19], ![297, -2, -10]]]
  hmulB := by decide  
  f := ![![![-18, -8, 1]], ![![-1, -1, -1]], ![![-16, -7, 1]]]
  g := ![![![8, -1, -9], ![-17, 2, 19], ![9, -2, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-18, -8, 1]] ![![266, -1, -9]]
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
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2116, 2, 75]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-2116, 2, 75]] 
 ![![67, 0, 0], ![0, 67, 0], ![37, 17, 1]] where
  M :=![![![-2116, 2, 75], ![4729, 65, -209], ![-2874, -167, 203]]]
  hmulB := by decide  
  f := ![![![324, 193, 79]], ![![5363, 3194, 1307]], ![![1674, 997, 408]]]
  g := ![![![-73, -19, 75], ![186, 54, -209], ![-155, -54, 203]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [45, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 66], [0, 1]]
 g := ![![[58, 21], [37, 56], [16], [22], [9], [1]], ![[54, 46], [4, 11], [16], [22], [9], [1]]]
 h' := ![![[3, 66], [10, 50], [39, 49], [25, 63], [12, 25], [22, 3], [0, 1]], ![[0, 1], [26, 17], [52, 18], [13, 4], [20, 42], [31, 64], [3, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [47, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [45, 64, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-378, -27, 93]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57, -24, 93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-324, -193, -79]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-324, -193, -79]] 
 ![![67, 0, 0], ![1, 1, 0], ![50, 0, 1]] where
  M :=![![![-324, -193, -79], ![-5363, -3194, -1307], ![-8999, -5360, -2194]]]
  hmulB := by decide  
  f := ![![![2116, -2, -75]], ![![-39, -1, 2]], ![![1622, 1, -59]]]
  g := ![![![57, -193, -79], ![943, -3194, -1307], ![1583, -5360, -2194]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-2116, 2, 75]] ![![-324, -193, -79]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -3, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-10, -3, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![61, 68, 1]] where
  M :=![![![-10, -3, 1], ![57, 10, -27], ![-229, -90, 30]]]
  hmulB := by decide  
  f := ![![![-30, 0, 1]], ![![63, -1, -3]], ![![34, -1, -2]]]
  g := ![![![-1, -1, 1], ![24, 26, -27], ![-29, -30, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [45, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 70], [0, 1]]
 g := ![![[70, 30], [32, 20], [53, 64], [60], [37], [1]], ![[0, 41], [9, 51], [22, 7], [60], [37], [1]]]
 h' := ![![[45, 70], [51, 32], [29, 34], [23, 8], [5, 29], [26, 45], [0, 1]], ![[0, 1], [0, 39], [68, 37], [28, 63], [32, 42], [63, 26], [45, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [26, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [45, 26, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4488, 8560, 12672]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10824, -12016, 12672]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-30, 0, 1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-30, 0, 1]] 
 ![![71, 0, 0], ![27, 1, 0], ![41, 0, 1]] where
  M :=![![![-30, 0, 1], ![63, -1, -3], ![-40, -3, 1]]]
  hmulB := by decide  
  f := ![![![-10, -3, 1]], ![![-3, -1, 0]], ![![-9, -3, 1]]]
  g := ![![![-1, 0, 1], ![3, -1, -3], ![0, -3, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-10, -3, 1]] ![![-30, 0, 1]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 30, 12]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![59, 30, 12]] 
 ![![73, 0, 0], ![20, 1, 0], ![34, 0, 1]] where
  M :=![![![59, 30, 12], ![816, 497, 204], ![1410, 834, 341]]]
  hmulB := by decide  
  f := ![![![659, 222, -156]], ![![52, 17, -12]], ![![584, 198, -139]]]
  g := ![![![-13, 30, 12], ![-220, 497, 204], ![-368, 834, 341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, -3, -1]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-12, -3, -1]] 
 ![![73, 0, 0], ![59, 1, 0], ![54, 0, 1]] where
  M :=![![![-12, -3, -1], ![-69, -50, -21], ![-149, -84, -34]]]
  hmulB := by decide  
  f := ![![![-64, -18, 13]], ![![-41, -11, 8]], ![![-70, -21, 15]]]
  g := ![![![3, -3, -1], ![55, -50, -21], ![91, -84, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9705, -36, -328]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![9705, -36, -328]] 
 ![![73, 0, 0], ![67, 1, 0], ![71, 0, 1]] where
  M :=![![![9705, -36, -328], ![-20736, 85, 696], ![10852, -60, -355]]]
  hmulB := by decide  
  f := ![![![11585, 6900, 2824]], ![![13259, 7897, 3232]], ![![15675, 9336, 3821]]]
  g := ![![![485, -36, -328], ![-1039, 85, 696], ![549, -60, -355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![59, 30, 12]] ![![-12, -3, -1]]
  ![![-4566, -2685, -1097]] where
 M := ![![![-4566, -2685, -1097]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![-4566, -2685, -1097]] ![![9705, -36, -328]]
  ![![73, 0, 0]] where
 M := ![![![-541514, 1971, 18323]]]
 hmul := by decide  
 g := ![![![![-7418, 27, 251]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9786, -56, -319]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![9786, -56, -319]] 
 ![![79, 0, 0], ![9, 1, 0], ![46, 0, 1]] where
  M :=![![![9786, -56, -319], ![-20209, 367, 509], ![9232, -667, 65]]]
  hmulB := by decide  
  f := ![![![363358, 216413, 88569]], ![![117505, 69985, 28642]], ![![339313, 202092, 82708]]]
  g := ![![![316, -56, -319], ![-594, 367, 509], ![155, -667, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1388, -5, -47]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![1388, -5, -47]] 
 ![![79, 0, 0], ![61, 1, 0], ![6, 0, 1]] where
  M :=![![![1388, -5, -47], ![-2971, 10, 101], ![1565, -4, -54]]]
  hmulB := by decide  
  f := ![![![-136, -82, -35]], ![![-135, -81, -34]], ![![-58, -35, -15]]]
  g := ![![![25, -5, -47], ![-53, 10, 101], ![27, -4, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![9786, -56, -319]] ![![9786, -56, -319]]
  ![![93952492, -355795, -3170973]] where
 M := ![![![93952492, -355795, -3170973]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI79N1 : IdealMulLeCertificate' Table 
  ![![93952492, -355795, -3170973]] ![![1388, -5, -47]]
  ![![79, 0, 0]] where
 M := ![![![126500553096, -460636518, -4280469877]]]
 hmul := by decide  
 g := ![![![![1601272824, -5830842, -54183163]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB198I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB198I1 : PrimesBelowBoundCertificateInterval O 31 79 198 where
  m := 11
  g := ![2, 3, 2, 2, 2, 1, 2, 2, 2, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB198I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
    · exact ![I79N0, I79N0, I79N1]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
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
      exact NI41N1
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
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
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I43N1, I47N1, I53N1, I61N1, I67N1, I71N1, I73N0, I73N1, I73N2, I79N0, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N1], [I43N1], [I47N1], [I53N1], [], [I61N1], [I67N1], [I71N1], [I73N0, I73N1, I73N2], [I79N0, I79N0, I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
