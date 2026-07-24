
import IdealArithmetic.Examples.NF3_1_225228_1.RI3_1_225228_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [13, 29, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 15, 13], [20, 21, 24], [0, 1]]
 g := ![![[30, 29, 34], [36, 30], [15, 14, 27], [0, 1], []], ![[10, 19, 27, 17], [11, 34], [19, 17, 24, 13], [24, 34], [20, 21]], ![[27, 2, 30, 15], [10, 16], [15, 13, 17, 29], [4, 3], [9, 21]]]
 h' := ![![[17, 15, 13], [2, 28, 21], [27, 12, 20], [0, 24, 8], [0, 0, 1], [0, 1]], ![[20, 21, 24], [14, 25, 28], [34, 17, 21], [11, 21, 36], [29, 27, 21], [17, 15, 13]], ![[0, 1], [30, 21, 25], [7, 8, 33], [6, 29, 30], [24, 10, 15], [20, 21, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 7], []]
 b := ![[], [27, 30, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [13, 29, 0, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38924, 0, -2553]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1052, 0, -69]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153828, 27718, -5385]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-153828, 27718, -5385]] 
 ![![41, 0, 0], ![0, 41, 0], ![29, 35, 1]] where
  M :=![![![-153828, 27718, -5385], ![-439984, -203879, 155538], ![2221571, -108493, -98392]]]
  hmulB := by decide  
  f := ![![![-900849922, -80767421, -78373509]], ![![-7371897670, -660941571, -641351544]], ![![-7228108609, -648049888, -628841965]]]
  g := ![![![57, 5273, -5385], ![-120746, -137749, 155538], ![123779, 81347, -98392]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [10, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 40], [0, 1]]
 g := ![![[21, 37], [16], [10], [16, 25], [1]], ![[0, 4], [16], [10], [14, 16], [1]]]
 h' := ![![[36, 40], [8, 18], [39, 37], [4, 16], [31, 36], [0, 1]], ![[0, 1], [0, 23], [18, 4], [6, 25], [15, 5], [36, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [14, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [10, 5, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3377, 710, 73]
  a := ![2, -5, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-134, -45, 73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![900849922, 80767421, 78373509]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![900849922, 80767421, 78373509]] 
 ![![41, 0, 0], ![34, 1, 0], ![24, 0, 1]] where
  M :=![![![900849922, 80767421, 78373509], ![7371897670, 660941571, 641351544], ![12211386781, 1094835214, 1062384764]]]
  hmulB := by decide  
  f := ![![![153828, -27718, 5385]], ![![138296, -18013, 672]], ![![35861, -13579, 5552]]]
  g := ![![![-90883088, 80767421, 78373509], ![-743720800, 660941571, 641351544], ![-1231957191, 1094835214, 1062384764]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-153828, 27718, -5385]] ![![900849922, 80767421, 78373509]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, 3, 3]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![34, 3, 3]] 
 ![![43, 0, 0], ![10, 1, 0], ![30, 0, 1]] where
  M :=![![![34, 3, 3], ![282, 25, 24], ![459, 42, 40]]]
  hmulB := by decide  
  f := ![![![-8, 6, -3]], ![![-8, 1, 0]], ![![3, 3, -2]]]
  g := ![![![-2, 3, 3], ![-16, 25, 24], ![-27, 42, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-102435, 4434, 4880]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-102435, 4434, 4880]] 
 ![![43, 0, 0], ![16, 1, 0], ![6, 0, 1]] where
  M :=![![![-102435, 4434, 4880], ![457828, -116183, 36364], ![705608, 68766, -93567]]]
  hmulB := by decide  
  f := ![![![-8370287937, -750454158, -728211016]], ![![-4707463460, -422056631, -409547052]], ![![-3806613538, -341289210, -331173543]]]
  g := ![![![-4713, 4434, 4880], ![48804, -116183, 36364], ![3878, 68766, -93567]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84364272, 7563840, 7339651]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![84364272, 7563840, 7339651]] 
 ![![43, 0, 0], ![17, 1, 0], ![8, 0, 1]] where
  M :=![![![84364272, 7563840, 7339651], ![690375572, 61896941, 60062342], ![1143591991, 102530925, 99491952]]]
  hmulB := by decide  
  f := ![![![-7518, -8505, 5689]], ![![8804, -3274, 1327]], ![![-11525, 600, 488]]]
  g := ![![![-2393912, 7563840, 7339651], ![-19590027, 61896941, 60062342], ![-32450450, 102530925, 99491952]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![34, 3, 3]] ![![-102435, 4434, 4880]]
  ![![7518, 8505, -5689]] where
 M := ![![![7518, 8505, -5689]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![7518, 8505, -5689]] ![![84364272, 7563840, 7339651]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35202399, -10198881, 8753894]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-35202399, -10198881, 8753894]] 
 ![![47, 0, 0], ![0, 47, 0], ![28, 24, 1]] where
  M :=![![![-35202399, -10198881, 8753894], ![784960486, -23558531, -43685498], ![-404309518, 141507291, -55600161]]]
  hmulB := by decide  
  f := ![![![-159397331797647, -14291072340879, -13867491036116]], ![![-1304391320004430, -116947696079773, -113481416117506]], ![![-807004522957540, -72353532439575, -70209004517251]]]
  g := ![![![-5964073, -4687071, 8753894], ![42726690, 21806243, -43685498], ![24521170, 31402365, -55600161]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [6, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 46], [0, 1]]
 g := ![![[42, 8], [23, 24], [36, 36], [38, 7], [1]], ![[0, 39], [38, 23], [35, 11], [13, 40], [1]]]
 h' := ![![[30, 46], [3, 14], [19, 20], [7, 6], [41, 30], [0, 1]], ![[0, 1], [0, 33], [8, 27], [46, 41], [1, 17], [30, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [6, 17, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1001747, 257705, 13779]
  a := ![-65, 2, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13105, -1553, 13779]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159397331797647, -14291072340879, -13867491036116]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-159397331797647, -14291072340879, -13867491036116]] 
 ![![47, 0, 0], ![42, 1, 0], ![18, 0, 1]] where
  M :=![![![-159397331797647, -14291072340879, -13867491036116], ![-1304391320004430, -116947696079773, -113481416117506], ![-2160695608563944, -193721293200861, -187979476479405]]]
  hmulB := by decide  
  f := ![![![-35202399, -10198881, 8753894]], ![![-14756176, -9615139, 6893150]], ![![-22084100, -895161, 2169573]]]
  g := ![![![14690266918497, -14291072340879, -13867491036116], ![120214412882152, -116947696079773, -113481416117506], ![199132537925564, -193721293200861, -187979476479405]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-35202399, -10198881, 8753894]] ![![-159397331797647, -14291072340879, -13867491036116]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13552, 1215, 1179]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![13552, 1215, 1179]] 
 ![![53, 0, 0], ![0, 53, 0], ![11, 16, 1]] where
  M :=![![![13552, 1215, 1179], ![110898, 9943, 9648], ![183699, 16470, 15982]]]
  hmulB := by decide  
  f := ![![![122, 0, -9]], ![![-828, 131, -18]], ![![-235, 37, -5]]]
  g := ![![![11, -333, 1179], ![90, -2725, 9648], ![149, -4514, 15982]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [5, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 52], [0, 1]]
 g := ![![[7, 9], [17], [34, 9], [1], [18, 1]], ![[10, 44], [17], [37, 44], [1], [36, 52]]]
 h' := ![![[18, 52], [36, 3], [42, 21], [39, 50], [16, 1], [0, 1]], ![[0, 1], [37, 50], [49, 32], [38, 3], [34, 52], [18, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [29, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [5, 35, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2192, 883, -233]
  a := ![-2, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 87, -233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-122, 0, 9]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-122, 0, 9]] 
 ![![53, 0, 0], ![8, 1, 0], ![10, 0, 1]] where
  M :=![![![-122, 0, 9], ![828, -131, 18], ![549, 135, -122]]]
  hmulB := by decide  
  f := ![![![-13552, -1215, -1179]], ![![-4138, -371, -360]], ![![-6023, -540, -524]]]
  g := ![![![-4, 0, 9], ![32, -131, 18], ![13, 135, -122]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![13552, 1215, 1179]] ![![-122, 0, 9]]
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
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63966, 5735, 5565]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![63966, 5735, 5565]] 
 ![![59, 0, 0], ![0, 59, 0], ![44, 41, 1]] where
  M :=![![![63966, 5735, 5565], ![523450, 46931, 45540], ![867085, 77740, 75436]]]
  hmulB := by decide  
  f := ![![![124, -40, 15]], ![![1300, 189, -210]], ![![949, 106, -134]]]
  g := ![![![-3066, -3770, 5565], ![-25090, -30851, 45540], ![-41561, -51104, 75436]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [39, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 58], [0, 1]]
 g := ![![[16, 35], [48, 16], [53], [58, 16], [25, 1]], ![[6, 24], [35, 43], [53], [45, 43], [50, 58]]]
 h' := ![![[25, 58], [16, 34], [44, 55], [39, 17], [28, 55], [0, 1]], ![[0, 1], [40, 25], [3, 4], [51, 42], [46, 4], [25, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [31, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [39, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![555, 135, -96]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![81, 69, -96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![124, -40, 15]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![124, -40, 15]] 
 ![![59, 0, 0], ![47, 1, 0], ![51, 0, 1]] where
  M :=![![![124, -40, 15], ![1300, 189, -210], ![-2765, 265, 44]]]
  hmulB := by decide  
  f := ![![![63966, 5735, 5565]], ![![59828, 5364, 5205]], ![![69989, 6275, 6089]]]
  g := ![![![21, -40, 15], ![53, 189, -210], ![-296, 265, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![63966, 5735, 5565]] ![![124, -40, 15]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-459838120023653, -41227665257875, -40005694797876]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-459838120023653, -41227665257875, -40005694797876]] 
 ![![61, 0, 0], ![1, 1, 0], ![31, 0, 1]] where
  M :=![![![-459838120023653, -41227665257875, -40005694797876], ![-3762979251920342, -337377094710027, -327377381143002], ![-6233292586394936, -558857756710265, -542293450539403]]]
  hmulB := by decide  
  f := ![![![23621649, -25848515, 13861902]], ![![20446223, 583742, -1860744]], ![![-13118299, -9303720, 6584321]]]
  g := ![![![13468296458498, -41227665257875, -40005694797876], ![110214699315127, -337377094710027, -327377381143002], ![182568231754702, -558857756710265, -542293450539403]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4152498, -17712279, 10999069]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-4152498, -17712279, 10999069]] 
 ![![61, 0, 0], ![13, 1, 0], ![7, 0, 1]] where
  M :=![![![-4152498, -17712279, 10999069], ![976489790, 20272991, -84275536], ![-958586459, 182698314, -39577056]]]
  hmulB := by decide  
  f := ![![![14594653038551808, 1308511503999042, 1269727779661165]], ![![5068237184229488, 454402488571805, 440934192113307]], ![![4918016790116485, 440934192113307, 427865090232427]]]
  g := ![![![2444486, -17712279, 10999069], ![21358519, 20272991, -84275536], ![-50108609, 182698314, -39577056]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -1, -1]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-10, -1, -1]] 
 ![![61, 0, 0], ![47, 1, 0], ![24, 0, 1]] where
  M :=![![![-10, -1, -1], ![-94, -7, -8], ![-153, -14, -12]]]
  hmulB := by decide  
  f := ![![![28, -2, -1]], ![![20, -1, -1]], ![![7, -1, 0]]]
  g := ![![![1, -1, -1], ![7, -7, -8], ![13, -14, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-459838120023653, -41227665257875, -40005694797876]] ![![-4152498, -17712279, 10999069]]
  ![![28, -2, -1]] where
 M := ![![![28, -2, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![28, -2, -1]] ![![-10, -1, -1]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [53, 58, 66, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 2, 14], [23, 64, 53], [0, 1]]
 g := ![![[8, 65, 54], [53, 20, 54], [3, 14], [24, 33], [1, 1], []], ![[13, 49, 22, 17], [36, 48, 62, 6], [11, 40], [65, 40], [12, 9], [51, 62]], ![[41, 0, 56, 66], [5, 13, 22, 53], [1, 17], [14, 17], [6, 4], [12, 62]]]
 h' := ![![[45, 2, 14], [5, 34, 11], [58, 32, 56], [63, 49, 58], [14, 23, 10], [0, 0, 1], [0, 1]], ![[23, 64, 53], [40, 29, 41], [45, 36, 12], [62, 2, 43], [31, 41, 24], [59, 33, 64], [45, 2, 14]], ![[0, 1], [12, 4, 15], [28, 66, 66], [9, 16, 33], [9, 3, 33], [27, 34, 2], [23, 64, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 37], []]
 b := ![[], [54, 13, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [53, 58, 66, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5642673, 460491, 290713]
  a := ![2, 18, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![84219, 6873, 4339]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![235583, 13856, -25744]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![235583, 13856, -25744]] 
 ![![71, 0, 0], ![0, 71, 0], ![32, 42, 1]] where
  M :=![![![235583, 13856, -25744], ![-2340736, 233615, 31648], ![-295632, -400016, 263295]]]
  hmulB := by decide  
  f := ![![![-1044638983, -93659104, -90883088]], ![![-8548562304, -766437687, -743720800]], ![![-5727162960, -513479738, -498260417]]]
  g := ![![![14921, 15424, -25744], ![-47232, -15431, 31648], ![-122832, -161386, 263295]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [3, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 70], [0, 1]]
 g := ![![[3, 24], [43, 60], [55, 1], [18], [10], [1]], ![[0, 47], [0, 11], [46, 70], [18], [10], [1]]]
 h' := ![![[62, 70], [13, 33], [48, 29], [32, 1], [50, 35], [68, 62], [0, 1]], ![[0, 1], [0, 38], [0, 42], [23, 70], [19, 36], [7, 9], [62, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [40, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [3, 9, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2134, 403, -9]
  a := ![-2, 4, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, 11, -9]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1044638983, 93659104, 90883088]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![1044638983, 93659104, 90883088]] 
 ![![71, 0, 0], ![30, 1, 0], ![26, 0, 1]] where
  M :=![![![1044638983, 93659104, 90883088], ![8548562304, 766437687, 743720800], ![14160505936, 1269587216, 1231957191]]]
  hmulB := by decide  
  f := ![![![-235583, -13856, 25744]], ![![-66574, -9145, 10432]], ![![-82106, 560, 5719]]]
  g := ![![![-58142175, 93659104, 90883088], ![-475793086, 766437687, 743720800], ![-788140810, 1269587216, 1231957191]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![235583, 13856, -25744]] ![![1044638983, 93659104, 90883088]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [54, 35, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 25, 39], [39, 47, 34], [0, 1]]
 g := ![![[21, 39, 61], [37, 3], [19, 55], [45, 57, 57], [0, 1], []], ![[31, 42, 61, 20], [14, 6], [37, 4], [17, 27, 46, 62], [65, 19], [52, 61]], ![[17, 66, 30, 13], [72, 55], [62, 57], [53, 56, 41, 42], [26, 41], [57, 61]]]
 h' := ![![[34, 25, 39], [47, 36, 34], [72, 20, 21], [52, 19, 37], [0, 19, 38], [0, 0, 1], [0, 1]], ![[39, 47, 34], [72, 18, 9], [5, 54, 15], [18, 9, 71], [66, 26, 45], [27, 17, 47], [34, 25, 39]], ![[0, 1], [51, 19, 30], [56, 72, 37], [51, 45, 38], [48, 28, 63], [49, 56, 25], [39, 47, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 19], []]
 b := ![[], [53, 4, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [54, 35, 0, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![304264, -1679, 10074]
  a := ![2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4168, -23, 138]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [77, 39, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 10, 54], [53, 68, 25], [0, 1]]
 g := ![![[50, 62, 1], [71, 2, 36], [14, 38, 49], [14, 61, 38], [74, 1], []], ![[16, 51, 61, 60], [64, 46, 50, 61], [77, 67, 54, 27], [35, 33, 41, 70], [2, 42], [9, 72]], ![[4, 7, 43, 42], [14, 55, 23, 9], [4, 22, 3, 8], [10, 43, 75, 65], [59, 21], [38, 72]]]
 h' := ![![[21, 10, 54], [63, 73, 1], [28, 77, 73], [28, 71, 7], [69, 39, 65], [0, 0, 1], [0, 1]], ![[53, 68, 25], [1, 74, 60], [76, 45, 37], [71, 68, 44], [71, 15, 48], [64, 55, 68], [21, 10, 54]], ![[0, 1], [23, 11, 18], [71, 36, 48], [49, 19, 28], [61, 25, 45], [41, 24, 10], [53, 68, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 11], []]
 b := ![[], [73, 67, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [77, 39, 5, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1441118, 0, -91640]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18242, 0, -1160]
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



lemma PB135I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB135I1 : PrimesBelowBoundCertificateInterval O 31 79 135 where
  m := 11
  g := ![1, 2, 3, 2, 2, 2, 3, 1, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB135I1_primes
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
