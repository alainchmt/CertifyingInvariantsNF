
import IdealArithmetic.Examples.NF3_1_516660_1.RI3_1_516660_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-19, 0, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-19, 0, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-19, 0, 1], ![198, 11, 0], ![-33, 33, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![4, 6, 5], ![-10, -1, 0]], ![![10, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![-10, 0, 1], ![99, 11, 0], ![-22, 33, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1328209882678200976, -300580651547455126, -109990935153653593]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-1328209882678200976, -300580651547455126, -109990935153653593]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-1328209882678200976, -300580651547455126, -109990935153653593], ![-21778205160423411414, -4928518588835263892, -1803483909284730756], ![-55885268146325546379, -12647120406494222349, -4627937937287808766]]]
  hmulB := by decide  
  f := ![![![-1978011428, -410315441, 206908700]], ![![19494955586, 1704309345, -1127491973]], ![![-44035222209, -2740738065, 2114624786]]]
  g := ![![![-513814615565372925, -300580651547455126, -109990935153653593], ![-8424843285794073761, -4928518588835263892, -1803483909284730756], ![-21619073869915662015, -12647120406494222349, -4627937937287808766]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-19, 0, 1]] ![![2, 0, 0], ![-19, 0, 1]]
  ![![-1978011428, -410315441, 206908700]] where
 M := ![![![4, 0, 0], ![-38, 0, 2]], ![![-38, 0, 2], ![328, 33, -8]]]
 hmul := by decide  
 g := ![![![![-2656419765356401952, -601161303094910252, -219981870307307186]], ![![-30649280375439727835, -6936088027092574955, -2538110169368390499]]], ![![![-30649280375439727835, -6936088027092574955, -2538110169368390499]], ![![-353625733320909062879, -80027301943587605486, -29284246119246011662]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-1978011428, -410315441, 206908700]] ![![-1328209882678200976, -300580651547455126, -109990935153653593]]
  ![![2, 0, 0]] where
 M := ![![![2, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-21, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-21, -1, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-21, -1, 1], ![198, 8, -6], ![-231, 3, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![12, -1, 4], ![-36, -4, 0]], ![![1, 1, -2], ![19, 2, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-7, -1, 1], ![66, 8, -6], ![-77, 3, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-767476957711520337895153223, -173683938815021428315536616, -63555850162291997405205122]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-767476957711520337895153223, -173683938815021428315536616, -63555850162291997405205122]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-767476957711520337895153223, -173683938815021428315536616, -63555850162291997405205122], ![-12584058332133815486230614156, -2847836401395301688366843499, -1042103632890128569893219696], ![-32292076830018606892104480942, -7307861219806278763837867506, -2674152462580280260051306883]]]
  hmulB := by decide  
  f := ![![![124880515094559, -3488749237804, -1608453186858]], ![![-22904233602922, 22053557258469, -8049800600180]], ![![-212564464639626, -52580477433478, 25542306496273]]]
  g := ![![![-140036360027159160421359997, -173683938815021428315536616, -63555850162291997405205122], ![-2296128509781070703165642386, -2847836401395301688366843499, -1042103632890128569893219696], ![-5892118130135349788142915310, -7307861219806278763837867506, -2674152462580280260051306883]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-21, -1, 1]] ![![3, 0, 0], ![-21, -1, 1]]
  ![![124880515094559, -3488749237804, -1608453186858]] where
 M := ![![![9, 0, 0], ![-63, -3, 3]], ![![-63, -3, 3], ![12, 16, -6]]]
 hmul := by decide  
 g := ![![![![-2302430873134561013685459669, -521051816445064284946609848, -190667550486875992215615366]], ![![-3591002385942864310075649103, -812662103295527080844755071, -297375976282019744648779625]]], ![![![-3591002385942864310075649103, -812662103295527080844755071, -297375976282019744648779625]], ![![-5600731942189216827268259840, -1267474123089137190209576780, -463804517569293175615378434]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![124880515094559, -3488749237804, -1608453186858]] ![![-767476957711520337895153223, -173683938815021428315536616, -63555850162291997405205122]]
  ![![3, 0, 0]] where
 M := ![![![3, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![0, 2, 6], ![198, 30, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![3, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-3, 0, 5]], ![![0, 1, 0], ![-4, 2, 6], ![33, 30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-232311238877, -2182828022, 6371914668]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-232311238877, -2182828022, 6371914668]] 
 ![![5, 0, 0], ![2, 1, 0], ![4, 0, 1]] where
  M :=![![![-232311238877, -2182828022, 6371914668], ![1261639104264, -43336626859, -13096968132], ![-642473132400, 144788343384, -41153798837]]]
  hmulB := by decide  
  f := ![![![3679755143214738201671, 832747303650775746098, 304725717386275462716]], ![![13539040465782403604222, 3063953715151065864289, 1121187051335441080404]], ![![33909407604393092052892, 7673871399574693127392, 2808085906869620786803]]]
  g := ![![![-50686648301, -2182828022, 6371914668], ![280140046102, -43336626859, -13096968132], ![-153486924764, 144788343384, -41153798837]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![3679755143214738201671, 832747303650775746098, 304725717386275462716]] where
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![5, 5, 0], ![1, 3, 6]]]
 hmul := by decide  
 g := ![![![![-1161556194385, -10914140110, 31859573340]], ![![1029327865387, -45519454881, -6725053464]]], ![![![1029327865387, -45519454881, -6725053464]], ![![-60446544097, 147307470341, -55968356550]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![3679755143214738201671, 832747303650775746098, 304725717386275462716]] ![![-232311238877, -2182828022, 6371914668]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-22, 2, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-22, 2, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![6, 2, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-22, 2, 1], ![198, 10, 12], ![363, 93, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -2, 7]], ![![-4, 0, 1], ![18, -2, 12], ![45, 11, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [1, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[4, 1], [3, 1]], ![[0, 6], [6, 6]]]
 h' := ![![[3, 6], [4, 1], [0, 1]], ![[0, 1], [0, 6], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [1, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4720, 5309, 3610]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2420, -273, 3610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![0, 3, 6], ![198, 30, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-2, -1, 0], ![8, 0, 0]], ![![2, -2, -5], ![-4, 6, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-6, 3, 6], ![18, 30, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-22, 2, 1]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![-154, 14, 7], ![154, 14, 14]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![2, 1, 0]]], ![![![-22, 2, 1]], ![![22, 2, 2]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-19, 0, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-19, 0, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![3, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-19, 0, 1], ![198, 11, 0], ![-33, 33, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, 0, 11]], ![![-2, 0, 1], ![18, 1, 0], ![-6, 3, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 10], [0, 1]]
 g := ![![[8, 3], [5, 3], [1]], ![[4, 8], [1, 8], [1]]]
 h' := ![![[6, 10], [1, 6], [9, 6], [0, 1]], ![[0, 1], [4, 5], [1, 5], [6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1054, 2596, 1950]
  a := ![-1, 1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-436, 236, 1950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![0, 1, 0]] 
 ![![11, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 1, 6], ![198, 30, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![-2, 2, 0]]]
  g := ![![![1, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 1, 6], ![18, 30, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-19, 0, 1]] ![![11, 0, 0], ![0, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![0, 11, 0]], ![![-209, 0, 11], ![198, 11, 0]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![0, 1, 0]]], ![![![-19, 0, 1]], ![![18, 1, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [7, 10, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 9, 11], [0, 3, 2], [0, 1]]
 g := ![![[10, 8, 10], [1, 12], [1]], ![[0, 7, 11, 7], [2, 12], [12, 3, 5, 5]], ![[0, 4, 7, 5], [], [2, 7, 9, 8]]]
 h' := ![![[8, 9, 11], [3, 7, 6], [6, 3, 8], [0, 1]], ![[0, 3, 2], [0, 11, 4], [12, 1, 5], [8, 9, 11]], ![[0, 1], [1, 8, 3], [12, 9], [0, 3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 4], []]
 b := ![[], [12, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [7, 10, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-241670, -8151, -18135]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18590, -627, -1395]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [14, 6, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 11, 9], [4, 5, 8], [0, 1]]
 g := ![![[11, 8, 4], [5, 9], [3, 1], []], ![[0, 16, 5, 9], [8, 1], [16, 8], [16, 13]], ![[12, 11, 6, 4], [10, 4], [10, 2], [0, 13]]]
 h' := ![![[16, 11, 9], [11, 16, 2], [9, 2, 3], [0, 0, 1], [0, 1]], ![[4, 5, 8], [8, 1, 1], [1, 6, 16], [15, 6, 5], [16, 11, 9]], ![[0, 1], [5, 0, 14], [14, 9, 15], [16, 11, 11], [4, 5, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 16], []]
 b := ![[], [13, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [14, 6, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18132574, -5178353, -2047582]
  a := ![1, -2, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1066622, -304609, -120446]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![359899, 9706, -12336]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![359899, 9706, -12336]] 
 ![![19, 0, 0], ![3, 1, 0], ![17, 0, 1]] where
  M :=![![![359899, 9706, -12336], ![-2442528, -475, 58236], ![2328876, -115908, -10181]]]
  hmulB := by decide  
  f := ![![![-6754854263, -1528657874, -559379016]], ![![-6895874103, -1560571381, -571057068]], ![![-21002488105, -4752969874, -1739245685]]]
  g := ![![![28447, 9706, -12336], ![-180585, -475, 58236], ![149983, -115908, -10181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1898990614675155039239373597556, 429751234112639055818973051447, 157258093227677975327024631479]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![1898990614675155039239373597556, 429751234112639055818973051447, 157258093227677975327024631479]] 
 ![![19, 0, 0], ![16, 1, 0], ![18, 0, 1]] where
  M :=![![![1898990614675155039239373597556, 429751234112639055818973051447, 157258093227677975327024631479], ![31137102459080239114750877032842, 7046484645618133354869085593373, 2578507404675834334913838308682], ![79901227277789159866364851347699, 18082054099892544860361004382217, 6616733411505494299050112541926]]]
  hmulB := by decide  
  f := ![![![21496213492748404, 1611916543542021, -1139050316825813]], ![![6231971218550710, 775120275167809, -450173989892678]], ![![39141051523475961, 2093859664987641, -1746221142888980]]]
  g := ![![![-410930253117119653144770452222, 429751234112639055818973051447, 157258093227677975327024631479], ![-6737883429209205925873872737758, 7046484645618133354869085593373, 2578507404675834334913838308682], ![-17290149459346866067490170764339, 18082054099892544860361004382217, 6616733411505494299050112541926]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-114907128328, -4029357109, 4301186291]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-114907128328, -4029357109, 4301186291]] 
 ![![19, 0, 0], ![18, 1, 0], ![0, 0, 1]] where
  M :=![![![-114907128328, -4029357109, 4301186291], ![851634885618, 10099103293, -24176142654], ![-939751855185, 21058434333, 14128460402]]]
  hmulB := by decide  
  f := ![![![651796493475357643568, 147504861423047026721, 53976187635848471023]], ![![1179980107076549202462, 267035499452037120103, 97715818209660770460]], ![![1443407808935805881421, 326650528140758439231, 119530638028990093382]]]
  g := ![![![-2230457914, -4029357109, 4301186291], ![35255317176, 10099103293, -24176142654], ![-69410719641, 21058434333, 14128460402]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![359899, 9706, -12336]] ![![1898990614675155039239373597556, 429751234112639055818973051447, 157258093227677975327024631479]]
  ![![-651796493475357643568, -147504861423047026721, -53976187635848471023]] where
 M := ![![![-651796493475357643568, -147504861423047026721, -53976187635848471023]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-651796493475357643568, -147504861423047026721, -53976187635848471023]] ![![-114907128328, -4029357109, 4301186291]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [8, 14, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 22, 19], [21, 0, 4], [0, 1]]
 g := ![![[2, 17, 13], [8], [11, 5, 1], []], ![[11, 20, 15, 11], [19, 16, 0, 17], [2, 17], [19, 16]], ![[7, 19, 8, 4], [18, 19, 7, 6], [4, 17, 22, 4], [11, 16]]]
 h' := ![![[7, 22, 19], [5, 19, 6], [4, 13], [0, 0, 1], [0, 1]], ![[21, 0, 4], [3, 17, 16], [3, 10, 17], [12, 6], [7, 22, 19]], ![[0, 1], [15, 10, 1], [1, 0, 6], [8, 17, 22], [21, 0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 8], []]
 b := ![[], [8, 11, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [8, 14, 18, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11616058, -3224646, -1255915]
  a := ![0, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-505046, -140202, -54605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀

instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1188704351793176, -46724040789515, 46459732591317]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1188704351793176, -46724040789515, 46459732591317]] 
 ![![29, 0, 0], ![15, 1, 0], ![18, 0, 1]] where
  M :=![![![-1188704351793176, -46724040789515, 46459732591317], ![9199027053080766, 158363585156819, -280344244737090], ![-10784531251837431, 131449951828011, 205087625946334]]]
  hmulB := by decide  
  f := ![![![69329649182112713072260779536, 15689652211212196986515868497, 5741286107613500230520870727]], ![![75059289208247025576794624034, 16986298889307340405935889562, 6215765685568127081962354203]], ![![143621461432648218311160250347, 32502267161704515964136221443, 11893495943019335315078019808]]]
  g := ![![![-45659273330833, -46724040789515, 46459732591317], ![409302402792969, 158363585156819, -280344244737090], ![-567167510216952, 131449951828011, 205087625946334]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-10, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-10, 1, 0]] 
 ![![29, 0, 0], ![19, 1, 0], ![14, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-10, 1, 0], ![0, -9, 6], ![198, 30, -10]]]
  hmulB := by decide  
  f := ![![![111, -11, 0], ![319, 0, 0]], ![![81, -8, 0], ![233, 0, 0]], ![![66, -5, -1], ![190, 5, 0]]]
  g := ![![![1, 0, 0], ![-19, 29, 0], ![-14, 0, 29]], ![![-1, 1, 0], ![3, -9, 6], ![-8, 30, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-6, 1, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-6, 1, 0]] 
 ![![29, 0, 0], ![23, 1, 0], ![24, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-6, 1, 0], ![0, -5, 6], ![198, 30, -6]]]
  hmulB := by decide  
  f := ![![![43, -7, 0], ![203, 0, 0]], ![![37, -6, 0], ![175, 0, 0]], ![![36, -5, -1], ![170, 5, 0]]]
  g := ![![![1, 0, 0], ![-23, 29, 0], ![-24, 0, 29]], ![![-1, 1, 0], ![-1, -5, 6], ![-12, 30, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1188704351793176, -46724040789515, 46459732591317]] ![![29, 0, 0], ![-10, 1, 0]]
  ![![29, 0, 0], ![-25, 1, 1]] where
 M := ![![![-34472426202002104, -1354997182895935, 1347332245148193], ![21086070571012526, 625603993051969, -744941570650260]]]
 hmul := by decide  
 g := ![![![![-682618784922751, -66967463464332, 26216309916500], ![587059257569693, 0, 0]], ![![417470968052344, 33957948032819, -13302243818982], ![-359176499899782, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-25, 1, 1]] ![![29, 0, 0], ![-6, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-174, 29, 0]], ![![-725, 29, 29], ![348, 0, 0]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-6, 1, 0]]], ![![![-25, 1, 1]], ![![12, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-28, 11, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-28, 11, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![3, 11, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-28, 11, 1], ![198, 13, 66], ![2145, 363, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -11, 31]], ![![-1, 0, 1], ![0, -23, 66], ![69, 11, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 30], [0, 1]]
 g := ![![[8, 18], [6, 16], [14, 7], [3, 1]], ![[0, 13], [23, 15], [4, 24], [6, 30]]]
 h' := ![![[3, 30], [10, 7], [13, 27], [5, 21], [0, 1]], ![[0, 1], [0, 24], [1, 4], [6, 10], [3, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [18, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [19, 28, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![463335, 458833, 311460]
  a := ![1, 20, 101]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15195, -95717, 311460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-4, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-4, 1, 0]] 
 ![![31, 0, 0], ![27, 1, 0], ![29, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-4, 1, 0], ![0, -3, 6], ![198, 30, -4]]]
  hmulB := by decide  
  f := ![![![49, -12, 0], ![372, 0, 0]], ![![45, -11, 0], ![342, 0, 0]], ![![43, -8, -5], ![326, 26, 0]]]
  g := ![![![1, 0, 0], ![-27, 31, 0], ![-29, 0, 31]], ![![-1, 1, 0], ![-3, -3, 6], ![-16, 30, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-28, 11, 1]] ![![31, 0, 0], ![-4, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-124, 31, 0]], ![![-868, 341, 31], ![310, -31, 62]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-4, 1, 0]]], ![![![-28, 11, 1]], ![![10, -1, 2]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB204I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB204I0 : PrimesBelowBoundCertificateInterval O 1 31 204 where
  m := 11
  g := ![3, 3, 3, 2, 2, 1, 1, 3, 1, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB204I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0, I31N1]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![12167]
    · exact ![29, 29, 29]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I19N0, I19N1, I19N2, I29N0, I29N1, I29N2, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N0, I5N1], [I7N0, I7N1], [I11N0, I11N1], [], [], [I19N0, I19N1, I19N2], [], [I29N0, I29N1, I29N2], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
