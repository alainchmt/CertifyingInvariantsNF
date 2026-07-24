
import IdealArithmetic.Examples.NF3_1_863379_1.RI3_1_863379_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![339013, 9810, 5980]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![339013, 9810, 5980]] 
 ![![37, 0, 0], ![1, 1, 0], ![36, 0, 1]] where
  M :=![![![339013, 9810, 5980], ![556140, 16093, 9810], ![912330, 26400, 16093]]]
  hmulB := by decide  
  f := ![![![649, -330, -40]], ![![-83, 67, -10]], ![![-198, 60, 37]]]
  g := ![![![3079, 9810, 5980], ![5051, 16093, 9810], ![8286, 26400, 16093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14256184475278, 7784098793421, -10042507762556]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![14256184475278, 7784098793421, -10042507762556]] 
 ![![37, 0, 0], ![7, 1, 0], ![25, 0, 1]] where
  M :=![![![14256184475278, 7784098793421, -10042507762556], ![-933953221917708, 556551603653302, 7784098793421], ![723921187788153, -1354294556762442, 556551603653302]]]
  hmulB := by decide  
  f := ![![![320291650154293312881344997286, 9268260932599970434832195610, 5649765993977013851594243153]], ![![74796480770808526442369718763, 2164381432641469133488682062, 1319368186228082902594375613]], ![![239709176232138650607378895240, 6936450551201706637517052447, 4228336116998916518516539077]]]
  g := ![![![5698113161763, 7784098793421, -10042507762556], ![-135795051819631, 556551603653302, 7784098793421], ![-100265054221819, -1354294556762442, 556551603653302]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-862857024728026751708212, -24968443756975097751930, -15220316463523778502001]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![-862857024728026751708212, -24968443756975097751930, -15220316463523778502001]] 
 ![![37, 0, 0], ![29, 1, 0], ![10, 0, 1]] where
  M :=![![![-862857024728026751708212, -24968443756975097751930, -15220316463523778502001], ![-1415489431107711400686093, -40959935697742712600158, -24968443756975097751930], ![-2322065269398684090929490, -67193468231056122081873, -40959935697742712600158]]]
  hmulB := by decide  
  f := ![![![536522139926, -466653522933, 85097191258]], ![![634410293104, -475450766299, 54085541177]], ![![-1027933952257, 768832264758, -86696061498]]]
  g := ![![![363000239445645084264, -24968443756975097751930, -15220316463523778502001], ![595490316123736276697, -40959935697742712600158, -24968443756975097751930], ![976882872415420958011, -67193468231056122081873, -40959935697742712600158]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![339013, 9810, 5980]] ![![14256184475278, 7784098793421, -10042507762556]]
  ![![-536522139926, 466653522933, -85097191258]] where
 M := ![![![-536522139926, 466653522933, -85097191258]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-536522139926, 466653522933, -85097191258]] ![![-862857024728026751708212, -24968443756975097751930, -15220316463523778502001]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [29, 26, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 25, 31], [40, 15, 10], [0, 1]]
 g := ![![[33, 1, 25], [29, 4], [], [35, 26, 1], []], ![[25, 20, 1, 8], [37, 23], [18, 36], [38, 22, 1, 5], [9, 18]], ![[15, 11, 15, 31], [33, 36], [19, 36], [15, 38, 7, 18], [30, 18]]]
 h' := ![![[27, 25, 31], [16, 13, 5], [18, 12, 2], [10, 17], [0, 0, 1], [0, 1]], ![[40, 15, 10], [1, 15, 27], [7, 12, 33], [18, 15, 35], [17, 20, 15], [27, 25, 31]], ![[0, 1], [4, 13, 9], [31, 17, 6], [34, 9, 6], [33, 21, 25], [40, 15, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 25], []]
 b := ![[], [2, 19, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [29, 26, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9143, 820, -3854]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![223, 20, -94]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16541993290571209, 18375188242607732, -5054340975218120]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-16541993290571209, 18375188242607732, -5054340975218120]] 
 ![![43, 0, 0], ![0, 43, 0], ![24, 20, 1]] where
  M :=![![![-16541993290571209, 18375188242607732, -5054340975218120], ![-470053710695285160, 256392419371207271, 18375188242607732], ![1708892506562519076, -1462313875796102688, 256392419371207271]]]
  hmulB := by decide  
  f := ![![![-2153659661594225834890219712047699, -62320324910295435037704106955516, -37989354742196985811912106538008]], ![![-3533009991024319680507825908034744, -102234505515588601046965958995267, -62320324910295435037704106955516]], ![![-2980088881753611374558797051086108, -86234659395982061635256322773828, -52567105058935464215975317558553]]]
  g := ![![![2436330002666597, 2778186226673724, -5054340975218120], ![-21187400663206296, -2583984778626683, 18375188242607732], ![-103361059496429196, -153259587516749956, 256392419371207271]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [13, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 42], [0, 1]]
 g := ![![[25, 10], [12, 36], [14], [1, 17], [1]], ![[0, 33], [8, 7], [14], [23, 26], [1]]]
 h' := ![![[19, 42], [16, 15], [30, 6], [30, 10], [30, 19], [0, 1]], ![[0, 1], [0, 28], [15, 37], [5, 33], [4, 24], [19, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [40, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [13, 24, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1126, 1441, -416]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![206, 227, -416]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2153659661594225834890219712047699, -62320324910295435037704106955516, -37989354742196985811912106538008]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-2153659661594225834890219712047699, -62320324910295435037704106955516, -37989354742196985811912106538008]] 
 ![![43, 0, 0], ![23, 1, 0], ![30, 0, 1]] where
  M :=![![![-2153659661594225834890219712047699, -62320324910295435037704106955516, -37989354742196985811912106538008], ![-3533009991024319680507825908034744, -102234505515588601046965958995267, -62320324910295435037704106955516], ![-5795790216657475458506481946862988, -167712445868366188471804132436880, -102234505515588601046965958995267]]]
  hmulB := by decide  
  f := ![![![-16541993290571209, 18375188242607732, -5054340975218120]], ![![-19779524566940069, 15791203463981049, -2276154748544396]], ![![28200760647567042, -21187400663206296, 2436330002666597]]]
  g := ![![![9753219851359970821728789396963, -62320324910295435037704106955516, -37989354742196985811912106538008], ![15999846119606539411709636221439, -102234505515588601046965958995267, -62320324910295435037704106955516], ![26247237297269881575674229512634, -167712445868366188471804132436880, -102234505515588601046965958995267]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-16541993290571209, 18375188242607732, -5054340975218120]] ![![-2153659661594225834890219712047699, -62320324910295435037704106955516, -37989354742196985811912106538008]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![248534534074, 7191829420, 4384010505]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![248534534074, 7191829420, 4384010505]] 
 ![![47, 0, 0], ![0, 47, 0], ![16, 44, 1]] where
  M :=![![![248534534074, 7191829420, 4384010505], ![407712976965, 11797966804, 7191829420], ![668840136060, 19354188285, 11797966804]]]
  hmulB := by decide  
  f := ![![![77228, -56165, 5540]], ![![515220, -221932, -56165]], ![![397489, -151394, -55416]]]
  g := ![![![3795539702, -3951162400, 4384010505], ![6226461835, -6481755908, 7191829420], ![10214312068, -10633113853, 11797966804]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [24, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 46], [0, 1]]
 g := ![![[16, 2], [29, 28], [5, 7], [13, 17], [1]], ![[0, 45], [40, 19], [43, 40], [18, 30], [1]]]
 h' := ![![[39, 46], [9, 7], [21, 34], [17, 17], [23, 39], [0, 1]], ![[0, 1], [0, 40], [31, 13], [22, 30], [40, 8], [39, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [12, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [24, 8, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3422, 81, 67]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50, -61, 67]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77228, 56165, -5540]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-77228, 56165, -5540]] 
 ![![47, 0, 0], ![3, 1, 0], ![38, 0, 1]] where
  M :=![![![-77228, 56165, -5540], ![-515220, 221932, 56165], ![5223345, -3548130, 221932]]]
  hmulB := by decide  
  f := ![![![-248534534074, -7191829420, -4384010505]], ![![-24538650621, -710073512, -432848105]], ![![-215173455976, -6226461835, -3795539702]]]
  g := ![![![-749, 56165, -5540], ![-70538, 221932, 56165], ![158177, -3548130, 221932]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![248534534074, 7191829420, 4384010505]] ![![-77228, 56165, -5540]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [23, 14, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 44, 13], [32, 8, 40], [0, 1]]
 g := ![![[1, 23, 36], [48, 47], [31, 42, 40], [0, 28], [1]], ![[19, 4, 27, 46], [0, 6], [27, 30, 5, 49], [1, 16], [22, 4, 52, 24]], ![[49, 39, 31, 43], [4, 11], [49, 52, 16, 15], [12, 25], [47, 23, 24, 29]]]
 h' := ![![[30, 44, 13], [2, 50, 6], [29, 32, 43], [52, 0, 26], [30, 39, 9], [0, 1]], ![[32, 8, 40], [9, 30, 9], [50, 25, 18], [13, 13, 49], [47, 51, 49], [30, 44, 13]], ![[0, 1], [21, 26, 38], [31, 49, 45], [38, 40, 31], [46, 16, 48], [32, 8, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 49], []]
 b := ![[], [18, 22, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [23, 14, 44, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-395168, 403701, -98845]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7456, 7617, -1865]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [17, 36, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 55, 32], [30, 3, 27], [0, 1]]
 g := ![![[44, 2, 1], [47, 19, 5], [30, 25], [10, 15, 41], [1]], ![[42, 39, 12, 43], [30, 42, 57, 2], [47, 27], [22, 47, 48, 10], [14, 58, 49, 23]], ![[54, 49, 40, 12], [41, 47, 20, 25], [31, 17], [38, 48, 3, 53], [28, 24, 6, 36]]]
 h' := ![![[19, 55, 32], [27, 53, 58], [11, 8, 8], [7, 28, 5], [42, 23, 49], [0, 1]], ![[30, 3, 27], [8, 41, 41], [52, 9, 44], [5, 39, 26], [13, 19, 57], [19, 55, 32]], ![[0, 1], [19, 24, 19], [55, 42, 7], [46, 51, 28], [33, 17, 12], [30, 3, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 30], []]
 b := ![[], [8, 31, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [17, 36, 10, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8201, 885, -3599]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139, 15, -61]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-108940126893601404356609580457455537661892179678, -3152394143256797160372077337202581650828190848, -1921643052532007262287087642917486716495618765]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-108940126893601404356609580457455537661892179678, -3152394143256797160372077337202581650828190848, -1921643052532007262287087642917486716495618765]] 
 ![![61, 0, 0], ![5, 1, 0], ![36, 0, 1]] where
  M :=![![![-108940126893601404356609580457455537661892179678, -3152394143256797160372077337202581650828190848, -1921643052532007262287087642917486716495618765], ![-178712803885476675392699150791326264634092545145, -5171402056873012193106847739911254971128766368, -3152394143256797160372077337202581650828190848], ![-293172655322882135914603192359840093527021748864, -8483520149609628732606974582386855489370239353, -5171402056873012193106847739911254971128766368]]]
  hmulB := by decide  
  f := ![![![-533509071145467803870080, 342060584212331619541019, -10267192861149429263584]], ![![-59383512980561244932192, 28380692859315729083091, 4765977375517778249559]], ![![206644389680491797999867, -116589171342768296282814, -5716386879422591428288]]]
  g := ![![![-393426332560084542826459649613329633014900818, -3152394143256797160372077337202581650828190848, -1921643052532007262287087642917486716495618765], ![-645403351538801912356887343483230333584161357, -5171402056873012193106847739911254971128766368, -3152394143256797160372077337202581650828190848], ![-1058763615203369726224947554280338313434999391, -8483520149609628732606974582386855489370239353, -5171402056873012193106847739911254971128766368]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-355159231519765, -10277222115410, -6264810674024]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-355159231519765, -10277222115410, -6264810674024]] 
 ![![61, 0, 0], ![8, 1, 0], ![58, 0, 1]] where
  M :=![![![-355159231519765, -10277222115410, -6264810674024], ![-582627392684232, -16859455122469, -10277222115410], ![-955781656733130, -27657398452092, -16859455122469]]]
  hmulB := by decide  
  f := ![![![-8718241, 9289082, -2422844]], ![![-4837220, 3220131, -165470]], ![![5872568, -3084724, -301797]]]
  g := ![![![1482255155687, -10277222115410, -6264810674024], ![2431592311300, -16859455122469, -10277222115410], ![3988949639128, -27657398452092, -16859455122469]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139485554831484676, -4036285422626249, -2460447357770044]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-139485554831484676, -4036285422626249, -2460447357770044]] 
 ![![61, 0, 0], ![48, 1, 0], ![14, 0, 1]] where
  M :=![![![-139485554831484676, -4036285422626249, -2460447357770044], ![-228821604272614092, -6621397511902300, -4036285422626249], ![-375374544304241157, -10862191450796646, -6621397511902300]]]
  hmulB := by decide  
  f := ![![![-184529146, 29000276, 50891199]], ![![-67615041, -25256404, 40520948]], ![![1862584, 58571647, -36396346]]]
  g := ![![![1454137843661572, -4036285422626249, -2460447357770044], ![2385466757630554, -6621397511902300, -4036285422626249], ![3913282139354591, -10862191450796646, -6621397511902300]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-108940126893601404356609580457455537661892179678, -3152394143256797160372077337202581650828190848, -1921643052532007262287087642917486716495618765]] ![![-355159231519765, -10277222115410, -6264810674024]]
  ![![42364434109994660777171285760113412191538704450564487309828856, 1225897176539636223872384015464083324851081938776027266308072, 747284979403698534358249386081089893791165135661266466582737]] where
 M := ![![![42364434109994660777171285760113412191538704450564487309828856, 1225897176539636223872384015464083324851081938776027266308072, 747284979403698534358249386081089893791165135661266466582737]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![42364434109994660777171285760113412191538704450564487309828856, 1225897176539636223872384015464083324851081938776027266308072, 747284979403698534358249386081089893791165135661266466582737]] ![![-139485554831484676, -4036285422626249, -2460447357770044]]
  ![![61, 0, 0]] where
 M := ![![![-6470250114172615117399463466192463293772294755783619066063824639550048928267989, -187229252865156882105653200035074939757032567534847709734136501747964729706846, -114131601775970710646119404838692280412750877168955856103455120187733201966692]]]
 hmul := by decide  
 g := ![![![![-106069674002829756022942024035942021209381881242354410919079092451640146365049, -3069332014182899706650052459591392455033320779259798520231745930294503765686, -1871009865179847715510154177683480006766407822441899280384510167012019704372]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-742962380, 1338393341, -539782984]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-742962380, 1338393341, -539782984]] 
 ![![67, 0, 0], ![0, 67, 0], ![24, 29, 1]] where
  M :=![![![-742962380, 1338393341, -539782984], ![-50199817512, 28405318756, 1338393341], ![124470580713, -122473057926, 28405318756]]]
  hmulB := by decide  
  f := ![![![14489242668806433706, 419274376043109364, 255582156042059555]], ![![23769140511911538615, 687806242535217736, 419274376043109364]], ![![16060289789086540293, 464735675584172717, 283294550638728636]]]
  g := ![![![182266108, 253613431, -539782984], ![-1228675488, -155344599, 1338393341], ![-8317269693, -14122795550, 28405318756]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [11, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 66], [0, 1]]
 g := ![![[57, 60], [64, 9], [26], [29], [40], [1]], ![[24, 7], [49, 58], [26], [29], [40], [1]]]
 h' := ![![[43, 66], [33, 44], [65, 64], [4, 19], [16, 37], [56, 43], [0, 1]], ![[0, 1], [49, 23], [3, 3], [17, 48], [66, 30], [29, 24], [43, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [11, 24, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3570, -1465, 333]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -166, 333]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14489242668806433706, 419274376043109364, 255582156042059555]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![14489242668806433706, 419274376043109364, 255582156042059555]] 
 ![![67, 0, 0], ![38, 1, 0], ![30, 0, 1]] where
  M :=![![![14489242668806433706, 419274376043109364, 255582156042059555], ![23769140511911538615, 687806242535217736, 419274376043109364], ![38992516972009170852, 1128324205583632959, 687806242535217736]]]
  hmulB := by decide  
  f := ![![![-742962380, 1338393341, -539782984]], ![![-1170632656, 1183048742, -286169553]], ![![1525100139, -1228675488, 182266108]]]
  g := ![![![-135979825404380728, 419274376043109364, 255582156042059555], ![-223070566951045019, 687806242535217736, 419274376043109364], ![-365940150988439010, 1128324205583632959, 687806242535217736]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-742962380, 1338393341, -539782984]] ![![14489242668806433706, 419274376043109364, 255582156042059555]]
  ![![67, 0, 0]] where
 M := ![![![67, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-52940984005806400594491934, -1531950188392503142818738, -933849418115018830050409]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-52940984005806400594491934, -1531950188392503142818738, -933849418115018830050409]] 
 ![![71, 0, 0], ![0, 71, 0], ![12, 61, 1]] where
  M :=![![![-52940984005806400594491934, -1531950188392503142818738, -933849418115018830050409], ![-86847995884696751194688037, -2513115427595383771769848, -1531950188392503142818738], ![-142471367520502792282142634, -4122685711501581482476185, -2513115427595383771769848]]]
  hmulB := by decide  
  f := ![![![-1123851058994, 519436983129, 100972709228]], ![![9390461958204, -6576377357306, 519436983129]], ![![8558304312303, -5825139579280, 370717621469]]]
  g := ![![![-587813957583467248364606, 780744567839769654792341, -933849418115018830050409], ![-964290051042066387054411, 1280786564286581801974270, -1531950188392503142818738], ![-1581887075906453338322598, 2101089512279110261908233, -2513115427595383771769848]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [10, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 70], [0, 1]]
 g := ![![[19, 64], [61, 60], [38, 58], [64], [32], [1]], ![[0, 7], [21, 11], [23, 13], [64], [32], [1]]]
 h' := ![![[23, 70], [29, 8], [46, 42], [48, 22], [64, 63], [61, 23], [0, 1]], ![[0, 1], [0, 63], [18, 29], [57, 49], [22, 8], [22, 48], [23, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [6, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [10, 48, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-595, 555, -91]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 86, -91]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1123851058994, 519436983129, 100972709228]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-1123851058994, 519436983129, 100972709228]] 
 ![![71, 0, 0], ![10, 1, 0], ![42, 0, 1]] where
  M :=![![![-1123851058994, 519436983129, 100972709228], ![9390461958204, -6576377357306, 519436983129], ![48307639430997, -18659135130762, -6576377357306]]]
  hmulB := by decide  
  f := ![![![-52940984005806400594491934, -1531950188392503142818738, -933849418115018830050409]], ![![-8679687830179728973797287, -251163624105921340844468, -153104850275249175258068]], ![![-33323840785413684750011322, -964290051042066387054411, -587813957583467248364606]]]
  g := ![![![-148719361660, 519436983129, 100972709228], ![751237778026, -6576377357306, 519436983129], ![7198687883739, -18659135130762, -6576377357306]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-52940984005806400594491934, -1531950188392503142818738, -933849418115018830050409]] ![![-1123851058994, 519436983129, 100972709228]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [52, 64, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 32, 25], [40, 40, 48], [0, 1]]
 g := ![![[33, 32, 48], [15, 72], [70, 61], [39, 72, 32], [3, 1], []], ![[14, 71, 47, 65], [49, 12], [67, 72], [59, 46, 66, 55], [16, 67], [44, 41]], ![[71, 56, 62, 37], [58, 16], [71, 71], [44, 44, 2, 4], [8, 2], [21, 41]]]
 h' := ![![[36, 32, 25], [42, 48, 11], [47, 49, 27], [16, 65, 39], [63, 48, 18], [0, 0, 1], [0, 1]], ![[40, 40, 48], [56, 46, 34], [66, 41, 42], [22, 69, 46], [68, 7, 22], [30, 57, 40], [36, 32, 25]], ![[0, 1], [31, 52, 28], [28, 56, 4], [17, 12, 61], [31, 18, 33], [70, 16, 32], [40, 40, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 49], []]
 b := ![[], [21, 36, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [52, 64, 70, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35113, -33872, 9198]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![481, -464, 126]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97936, -51875, -4770]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![97936, -51875, -4770]] 
 ![![79, 0, 0], ![0, 79, 0], ![64, 57, 1]] where
  M :=![![![97936, -51875, -4770], ![-443610, 355516, -51875], ![-4824375, 2357640, 355516]]]
  hmulB := by decide  
  f := ![![![3148027864, 91094300, 55529455]], ![![5164239315, 149437294, 91094300]], ![![6383635369, 184722887, 112603766]]]
  g := ![![![5104, 2785, -4770], ![36410, 41929, -51875], ![-349081, -226668, 355516]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [36, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 78], [0, 1]]
 g := ![![[74, 11], [14, 64], [39, 9], [15, 46], [10], [1]], ![[0, 68], [0, 15], [0, 70], [0, 33], [10], [1]]]
 h' := ![![[22, 78], [49, 66], [18, 71], [13, 3], [67, 58], [43, 22], [0, 1]], ![[0, 1], [0, 13], [0, 8], [0, 76], [0, 21], [53, 57], [22, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [47, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [36, 57, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3566, 1922, 6]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-50, 20, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3148027864, 91094300, 55529455]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![3148027864, 91094300, 55529455]] 
 ![![79, 0, 0], ![22, 1, 0], ![69, 0, 1]] where
  M :=![![![3148027864, 91094300, 55529455], ![5164239315, 149437294, 91094300], ![8471769900, 245147115, 149437294]]]
  hmulB := by decide  
  f := ![![![97936, -51875, -4770]], ![![21658, -9946, -1985]], ![![24471, -15465, 334]]]
  g := ![![![-34019989, 91094300, 55529455], ![-55808707, 149437294, 91094300], ![-91552404, 245147115, 149437294]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![97936, -51875, -4770]] ![![3148027864, 91094300, 55529455]]
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


lemma PB263I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB263I1 : PrimesBelowBoundCertificateInterval O 31 79 263 where
  m := 11
  g := ![3, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB263I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
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
    · exact ![37, 37, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
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
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N0, I37N1, I37N2, I43N1, I47N1, I61N0, I61N1, I61N2, I67N1, I71N1, I79N1]
  Il := ![[I37N0, I37N1, I37N2], [], [I43N1], [I47N1], [], [], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
