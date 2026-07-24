
import IdealArithmetic.Examples.NF3_1_355291_1.RI3_1_355291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![124662971623643514296687249, -27674746579178342898714418, 11925385551321047187450415]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![124662971623643514296687249, -27674746579178342898714418, 11925385551321047187450415]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 0, 1]] where
  M :=![![![124662971623643514296687249, -27674746579178342898714418, 11925385551321047187450415], ![-1526449350569094039993653120, 338866452425710062054785068, -146021683848964211541199266], ![2015918211565733851041792384, -447526838986814338135263578, 192844768576745850513585802]]]
  hmulB := by decide  
  f := ![![![-21529021864606, 449653504183, 1671816406984]], ![![-213992500093952, -4488001900331, 9834840157217]], ![![-146538585246991, -7332977416806, 3509327331935]]]
  g := ![![![56368793036161233554618417, -13837373289589171449357209, 11925385551321047187450415], ![-690213833360064914226226927, 169433226212855031027392534, -146021683848964211541199266], ![911536721494494000264103291, -223763419493407169067631789, 192844768576745850513585802]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3071, -3118, 1843]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2457, -1559, 1843]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21529021864606, 449653504183, 1671816406984]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-21529021864606, 449653504183, 1671816406984]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-21529021864606, 449653504183, 1671816406984], ![-213992500093952, -4488001900331, 9834840157217], ![-271548148629376, -15115608337795, 5346838256886]]]
  hmulB := by decide  
  f := ![![![124662971623643514296687249, -27674746579178342898714418, 11925385551321047187450415]], ![![-763224675284547019996826560, 169433226212855031027392534, -73010841924482105770599633]], ![![1007959105782866925520896192, -223763419493407169067631789, 96422384288372925256792901]]]
  g := ![![![-10764510932303, 449653504183, 1671816406984], ![-106996250046976, -4488001900331, 9834840157217], ![-135774074314688, -15115608337795, 5346838256886]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![124662971623643514296687249, -27674746579178342898714418, 11925385551321047187450415]] ![![-21529021864606, 449653504183, 1671816406984]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-181830110806240483972399533029, 40365652859764149759897660285, -17394051721710994119317543567]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-181830110806240483972399533029, 40365652859764149759897660285, -17394051721710994119317543567]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![-181830110806240483972399533029, 40365652859764149759897660285, -17394051721710994119317543567], ![2226438620379007247272645576576, -494261638324353868564585493121, 212983363131505071842013447727], ![-2940364945670803921994254939904, 652750802117937576790684785939, -281278275192848796722572045394]]]
  hmulB := by decide  
  f := ![![![-592479575208007, 34597763509041, 62835881626804]], ![![-8042992848230912, -5078167840286, 493527871070503]], ![![-4354662050865389, -112952472471052, 183761861619007]]]
  g := ![![![-54812019694843163284360663154, 13455217619921383253299220095, -17394051721710994119317543567], ![671151752415834058476877376283, -164753879441451289521528497707, 212983363131505071842013447727], ![-886362223492651708423894298170, 217583600705979192263561595313, -281278275192848796722572045394]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]], ![[0, 2]]]
 h' := ![![[0, 2], [0, 1]], ![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1406, -2727, 1528]
  a := ![-1, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-978, -909, 1528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![592479575208007, -34597763509041, -62835881626804]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![592479575208007, -34597763509041, -62835881626804]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![592479575208007, -34597763509041, -62835881626804], ![8042992848230912, 5078167840286, -493527871070503], ![12471506577388160, 373455180922197, -488449703230217]]]
  hmulB := by decide  
  f := ![![![181830110806240483972399533029, -40365652859764149759897660285, 17394051721710994119317543567]], ![![-620926132922175426442615503506, 137843444201608523014930057517, -59398419896027694534459453531]], ![![1101341722427761629979684668654, -244494035945821958770160035503, 105355459545423594987069044176]]]
  g := ![![![262448955159899, -34597763509041, -62835881626804], ![3006630751563782, 5078167840286, -493527871070503], ![4233831874001400, 373455180922197, -488449703230217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-181830110806240483972399533029, 40365652859764149759897660285, -17394051721710994119317543567]] ![![592479575208007, -34597763509041, -62835881626804]]
  ![![3, 0, 0]] where
 M := ![![![-3, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 3, 2], [3, 1, 3], [0, 1]]
 g := ![![[3, 2, 1], []], ![[3, 1, 1, 2], [0, 4]], ![[4, 0, 0, 2], [4, 4]]]
 h' := ![![[4, 3, 2], [0, 0, 1], [0, 1]], ![[3, 1, 3], [1, 1, 1], [4, 3, 2]], ![[0, 1], [1, 4, 3], [3, 1, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 3], []]
 b := ![[], [1, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [2, 1, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-267710, 34020, -34680]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-53542, 6804, -6936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145681897, -924496, 8308840]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-145681897, -924496, 8308840]] 
 ![![7, 0, 0], ![0, 1, 0], ![3, 0, 1]] where
  M :=![![![-145681897, -924496, 8308840], ![-1063531520, -51511169, 26763888], ![-945196032, -109875536, -24747281]]]
  hmulB := by decide  
  f := ![![![4215457913325457, -935817010833616, 403254954033512]], ![![-7373804873755648, 1636959062884991, -705385608528752]], ![![11544902430055669, -2562928228581824, 1104397006084887]]]
  g := ![![![-24372631, -924496, 8308840], ![-163403312, -51511169, 26763888], ![-124422027, -109875536, -24747281]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-127011, 28196, -12150]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-127011, 28196, -12150]] 
 ![![7, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![-127011, 28196, -12150], ![1555200, -345249, 148772], ![-2053888, 455956, -196477]]]
  hmulB := by decide  
  f := ![![![-1741, -92, 38]], ![![-1441, -189, -54]], ![![490, -236, -209]]]
  g := ![![![-26757, 28196, -12150], ![327629, -345249, 148772], ![-432686, 455956, -196477]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6303611067, -1399379756, 603009790]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![6303611067, -1399379756, 603009790]] 
 ![![7, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![6303611067, -1399379756, 603009790], ![-77185253120, 17134858025, -7383619132], ![101935355648, -22629294796, 9751238893]]]
  hmulB := by decide  
  f := ![![![-470747, -2732, 27042]], ![![-696231, -24755, 24310]], ![![-713524, -52212, 4589]]]
  g := ![![![1155673025, -1399379756, 603009790], ![-14150764381, 17134858025, -7383619132], ![18688326352, -22629294796, 9751238893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-145681897, -924496, 8308840]] ![![-127011, 28196, -12150]]
  ![![470747, 2732, -27042]] where
 M := ![![![470747, 2732, -27042]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![470747, 2732, -27042]] ![![6303611067, -1399379756, 603009790]]
  ![![7, 0, 0]] where
 M := ![![![-7, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [7, 9, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 4, 10], [4, 6, 1], [0, 1]]
 g := ![![[2, 8, 4], [3, 1, 1], []], ![[4, 7], [9, 9, 10, 8], [4, 1]], ![[6, 7, 7, 4], [8, 6, 10, 5], [2, 1]]]
 h' := ![![[8, 4, 10], [1, 10, 9], [0, 0, 1], [0, 1]], ![[4, 6, 1], [9, 9], [3, 10, 6], [8, 4, 10]], ![[0, 1], [4, 3, 2], [2, 1, 4], [4, 6, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 3], []]
 b := ![[], [1, 5, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [7, 9, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7905381, 1901427, -503844]
  a := ![1, 7, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-718671, 172857, -45804]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [8, 7, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 4, 5], [11, 8, 8], [0, 1]]
 g := ![![[4, 1, 3], [3, 12], [1]], ![[11, 4, 2, 11], [12, 12], [1, 4, 2, 8]], ![[9, 5, 6, 6], [4, 9], [3, 4, 1, 5]]]
 h' := ![![[7, 4, 5], [1, 8, 4], [5, 6, 5], [0, 1]], ![[11, 8, 8], [4, 10, 7], [10, 3, 5], [7, 4, 5]], ![[0, 1], [4, 8, 2], [7, 4, 3], [11, 8, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 4], []]
 b := ![[], [11, 3, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [8, 7, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3159416, 787917, -204581]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-243032, 60609, -15737]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [13, 14, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4, 12], [12, 12, 5], [0, 1]]
 g := ![![[13], [3, 4], [13, 1], []], ![[1, 2, 13, 7], [16, 16], [11, 8], [13, 8]], ![[5, 6, 15, 10], [5, 4], [1, 16], [3, 8]]]
 h' := ![![[1, 4, 12], [13, 9], [1, 9, 2], [0, 0, 1], [0, 1]], ![[12, 12, 5], [5, 2, 6], [14, 7, 13], [2, 11, 12], [1, 4, 12]], ![[0, 1], [2, 6, 11], [13, 1, 2], [3, 6, 4], [12, 12, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 1], []]
 b := ![[], [0, 16, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [13, 14, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1846064544, -492179070, 131010398]
  a := ![1, -41, 102]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108592032, -28951710, 7706494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1225832107, -26962837, 55388392]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-1225832107, -26962837, 55388392]] 
 ![![19, 0, 0], ![6, 1, 0], ![11, 0, 1]] where
  M :=![![![-1225832107, -26962837, 55388392], ![-7089714176, -535671284, 32813709], ![-3638471040, -961251911, -502857575]]]
  hmulB := by decide  
  f := ![![![300908603352624199, -66800664486157387, 28785220374202895]], ![![-98897715146432914, 21954949158441257, -9460655140056461]], ![![430314288589949535, -95528277009784066, 41164298691435259]]]
  g := ![![![-88069863, -26962837, 55388392], ![-222980909, -535671284, 32813709], ![403182829, -961251911, -502857575]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4401, 977, -421]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-4401, 977, -421]] 
 ![![19, 0, 0], ![14, 1, 0], ![16, 0, 1]] where
  M :=![![![-4401, 977, -421], ![53888, -11963, 5155], ![-71168, 15799, -6808]]]
  hmulB := by decide  
  f := ![![![-259, -37, -12]], ![![-110, -42, -25]], ![![112, -45, -41]]]
  g := ![![![-597, 977, -421], ![7310, -11963, 5155], ![-9654, 15799, -6808]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12985898255607, 2882824295348, -1242244119576]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-12985898255607, 2882824295348, -1242244119576]] 
 ![![19, 0, 0], ![17, 1, 0], ![4, 0, 1]] where
  M :=![![![-12985898255607, 2882824295348, -1242244119576], ![159007247305728, -35299056456987, 15210793589132], ![-209994262498816, 46617996683740, -20088262867855]]]
  hmulB := by decide  
  f := ![![![32660795, -344300, -2280424]], ![![44585673, 145049, -2647316]], ![![24558308, 1168452, -633919]]]
  g := ![![![-3001312357801, 2882824295348, -1242244119576], ![36749896458841, -35299056456987, 15210793589132], ![-48534060771104, 46617996683740, -20088262867855]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-1225832107, -26962837, 55388392]] ![![-4401, 977, -421]]
  ![![32660795, -344300, -2280424]] where
 M := ![![![32660795, -344300, -2280424]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![32660795, -344300, -2280424]] ![![-12985898255607, 2882824295348, -1242244119576]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![214368173, 7754951, -7384344]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![214368173, 7754951, -7384344]] 
 ![![23, 0, 0], ![3, 1, 0], ![0, 0, 1]] where
  M :=![![![214368173, 7754951, -7384344], ![945196032, 109875536, 24747281], ![-47437696, 173916589, 134622817]]]
  hmulB := by decide  
  f := ![![![10487791477160403, -2328253269799583, 1003272706546615]], ![![-4215457913325457, 935817010833616, -403254954033512]], ![![7373804873755648, -1636959062884991, 705385608528752]]]
  g := ![![![8308840, 7754951, -7384344], ![26763888, 109875536, 24747281], ![-24747281, 173916589, 134622817]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10014299538219639166678556459881, -2223139704425659484293660092833, 957977990290707570253551373616]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![10014299538219639166678556459881, -2223139704425659484293660092833, 957977990290707570253551373616]] 
 ![![23, 0, 0], ![7, 1, 0], ![19, 0, 1]] where
  M :=![![![10014299538219639166678556459881, -2223139704425659484293660092833, 957977990290707570253551373616], ![-122621182757210568992454575822848, 27221476544694400892348601848156, -11730065969816786109041415155367], ![161940699409273844997133916059776, -35950272632170745170272877504555, 15491410574877614783307186692789]]]
  hmulB := by decide  
  f := ![![![-11361129777049601, 1657653444860357, 1957736281532615]], ![![-14352963151109649, 730634047793504, 1440811878733968]], ![![-29505710901836645, 1140729042061710, 2688370329326119]]]
  g := ![![![320638941464165727039856565696, -2223139704425659484293660092833, 957977990290707570253551373616], ![-3926098484502279963787300035129, 27221476544694400892348601848156, -11730065969816786109041415155367], ![5185035083121494795922065714290, -35950272632170745170272877504555, 15491410574877614783307186692789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76995621, 5905959, 9233336]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-76995621, 5905959, 9233336]] 
 ![![23, 0, 0], ![12, 1, 0], ![1, 0, 1]] where
  M :=![![![-76995621, 5905959, 9233336], ![-1181867008, 6853198, 78275057], ![-1937829760, -45834483, 85128255]]]
  hmulB := by decide  
  f := ![![![4171097556300021, -925969165696833, 399011397556135]], ![![-44360357025436, 9847845136783, -4243556477377]], ![![3113986603404755, -691294206914592, 297887098017863]]]
  g := ![![![-6830455, 5905959, 9233336], ![-58364367, 6853198, 78275057], ![-64041053, -45834483, 85128255]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![214368173, 7754951, -7384344]] ![![10014299538219639166678556459881, -2223139704425659484293660092833, 957977990290707570253551373616]]
  ![![4171097556300021, -925969165696833, 399011397556135]] where
 M := ![![![4171097556300021, -925969165696833, 399011397556135]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![4171097556300021, -925969165696833, 399011397556135]] ![![-76995621, 5905959, 9233336]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7401, 1643, -708]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-7401, 1643, -708]] 
 ![![29, 0, 0], ![0, 29, 0], ![15, 25, 1]] where
  M :=![![![-7401, 1643, -708], ![90624, -20118, 8669], ![-119680, 26569, -11449]]]
  hmulB := by decide  
  f := ![![![-149, 5, 13]], ![![-1664, -21, 87]], ![![-1591, -19, 84]]]
  g := ![![![111, 667, -708], ![-1359, -8167, 8669], ![1795, 10786, -11449]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 28], [0, 1]]
 g := ![![[1, 1], [1], [], [28, 1]], ![[0, 28], [1], [], [27, 28]]]
 h' := ![![[28, 28], [28, 28], [0, 1], [1], [0, 1]], ![[0, 1], [0, 1], [28, 28], [1], [28, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [10, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7295, -7876, 4666]
  a := ![0, -8, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2665, -4294, 4666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, -5, -13]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![149, -5, -13]] 
 ![![29, 0, 0], ![24, 1, 0], ![15, 0, 1]] where
  M :=![![![149, -5, -13], ![1664, 21, -87], ![2304, 101, -66]]]
  hmulB := by decide  
  f := ![![![7401, -1643, 708]], ![![3000, -666, 287]], ![![7955, -1766, 761]]]
  g := ![![![16, -5, -13], ![85, 21, -87], ![30, 101, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-7401, 1643, -708]] ![![149, -5, -13]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54229681119, 118299971917, 86222983209]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![54229681119, 118299971917, 86222983209]] 
 ![![31, 0, 0], ![6, 1, 0], ![24, 0, 1]] where
  M :=![![![54229681119, 118299971917, 86222983209], ![-11036541850752, 647782580667, 1172991736255], ![-26178938256128, 266623892579, 1820774316922]]]
  hmulB := by decide  
  f := ![![![866718263144619468395329, -192408443146110121173463, 82911142881906141730432]], ![![-174590861613428042939462, 38758564690556666577732, -16701537845280949384191]], ![![1123125572557708922909544, -249329974990217030381819, 107439324611436081006075]]]
  g := ![![![-87900701529, 118299971917, 86222983209], ![-1389517387254, 647782580667, 1172991736255], ![-2305718232830, 266623892579, 1820774316922]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23506438569, -1653184575, 201833567]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-23506438569, -1653184575, 201833567]] 
 ![![31, 0, 0], ![18, 1, 0], ![19, 0, 1]] where
  M :=![![![-23506438569, -1653184575, 201833567], ![-25834696576, -16326715607, -10764957757], ![185772929024, -20607033129, -27091673364]]]
  hmulB := by decide  
  f := ![![![-220484205200980460295, 48946727518016401443, -21091741362754378444]], ![![-40934606425325414338, 9087340405773141886, -3915845721112306957]], ![![-250149616990069925467, 55532345867533696278, -23929564563308507149]]]
  g := ![![![77936968, -1653184575, 201833567], ![15244528443, -16326715607, -10764957757], ![34562623202, -20607033129, -27091673364]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![54229681119, 118299971917, 86222983209]] ![![54229681119, 118299971917, 86222983209]]
  ![![-3559907886378060665594175, 106037138267630788969773, 300433327697736582644404]] where
 M := ![![![-3559907886378060665594175, 106037138267630788969773, 300433327697736582644404]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-3559907886378060665594175, 106037138267630788969773, 300433327697736582644404]] ![![-23506438569, -1653184575, 201833567]]
  ![![31, 0, 0]] where
 M := ![![![136753698012348666722762327953920023, -2037092931017653091280472624956702, -9999235802669981917527238940006442]]]
 hmul := by decide  
 g := ![![![![4411409613301569894282655740449033, -65712675194117841654208794353442, -322555993634515545726685127096982]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB169I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB169I0 : PrimesBelowBoundCertificateInterval O 1 31 169 where
  m := 11
  g := ![2, 2, 1, 3, 1, 1, 1, 3, 3, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB169I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N0, I31N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 2]
    · exact ![9, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![2197]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I7N0, I7N1, I7N2, I19N0, I19N1, I19N2, I23N0, I23N1, I23N2, I29N1, I31N0, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0], [I7N0, I7N1, I7N2], [], [], [], [I19N0, I19N1, I19N2], [I23N0, I23N1, I23N2], [I29N1], [I31N0, I31N0, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
