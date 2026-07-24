
import IdealArithmetic.Examples.NF3_1_782987_1.RI3_1_782987_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29521281, 12747739, 23561]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![29521281, 12747739, 23561]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![29521281, 12747739, 23561], ![-2780198, 28508158, 12771300], ![-1507013400, -551946098, 41279458]]]
  hmulB := by decide  
  f := ![![![4112935256102882, -269612079330220, 81066759190031]], ![![-9565877584423658, 627064610931549, -188545320140189]], ![![8397702724110763, -550488143397101, 165520364920601]]]
  g := ![![![14748860, 6362089, 23561], ![-7775749, 7868429, 12771300], ![-774146429, -296612778, 41279458]]]
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
  c := ![355, -931, -389]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![372, -271, -389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4112935256102882, -269612079330220, 81066759190031]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![4112935256102882, -269612079330220, 81066759190031]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![4112935256102882, -269612079330220, 81066759190031], ![-9565877584423658, 627064610931549, -188545320140189], ![22248347776542302, -1458428818395531, 438519290791360]]]
  hmulB := by decide  
  f := ![![![29521281, 12747739, 23561]], ![![-1390099, 14254079, 6385650]], ![![-753506700, -275973049, 20639729]]]
  g := ![![![2056467628051441, -269612079330220, 81066759190031], ![-4782938792211829, 627064610931549, -188545320140189], ![11124173888271151, -1458428818395531, 438519290791360]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![29521281, 12747739, 23561]] ![![4112935256102882, -269612079330220, 81066759190031]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 2, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 2], [0, 1, 1], [0, 1]]
 g := ![![[1]], ![[2, 1, 1, 2]], ![[0, 2, 2, 1]]]
 h' := ![![[2, 1, 2], [0, 1]], ![[0, 1, 1], [2, 1, 2]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 2], []]
 b := ![[], [2, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-289563, 18306, -5916]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96521, 6102, -1972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀

instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99877366119469, 53629407250352, 4594642501516]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![99877366119469, 53629407250352, 4594642501516]] 
 ![![5, 0, 0], ![0, 5, 0], ![4, 2, 1]] where
  M :=![![![99877366119469, 53629407250352, 4594642501516], ![-542167815178888, -97692261445719, 58224049751868], ![-6870437870720424, -3045801954509212, -39468211693851]]]
  hmulB := by decide  
  f := ![![![36238932677854366041480556377, -2375542862603177489881995968, 714276458483079742912973508]], ![![-84284622101003409663730873944, 5525044963081937096222695533, -1661266404120097746969022460]], ![![34483184439116435796161025580, -2260449649617608462229100194, 679670316930792565393504437]]]
  g := ![![![16299759222681, 8888024449464, 4594642501516], ![-155012802837272, -42828072189891, 58224049751868], ![-1342513004789004, -593373106224302, -39468211693851]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [0, 1]]
 g := ![![[1, 4], [1]], ![[4, 1], [1]]]
 h' := ![![[2, 4], [2, 2], [0, 1]], ![[0, 1], [1, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-347, -1186, -398]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![249, -78, -398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36238932677854366041480556377, -2375542862603177489881995968, 714276458483079742912973508]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![36238932677854366041480556377, -2375542862603177489881995968, 714276458483079742912973508]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![36238932677854366041480556377, -2375542862603177489881995968, 714276458483079742912973508], ![-84284622101003409663730873944, 5525044963081937096222695533, -1661266404120097746969022460], ![196029435686171534142344650280, -12850166723839206544062908164, 3863778558961839349253673073]]]
  hmulB := by decide  
  f := ![![![99877366119469, 53629407250352, 4594642501516]], ![![-68482616587990, 1913310610997, 13482666950980]], ![![-1354112100920191, -598434509451772, -6974713838467]]]
  g := ![![![8055148388915528255666314961, -2375542862603177489881995968, 714276458483079742912973508], ![-18734689124609437221841448510, 5525044963081937096222695533, -1661266404120097746969022460], ![43573198114977621576243358707, -12850166723839206544062908164, 3863778558961839349253673073]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![99877366119469, 53629407250352, 4594642501516]] ![![36238932677854366041480556377, -2375542862603177489881995968, 714276458483079742912973508]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1080865099021660165617969, 70853117950321663366760, -21304062729721250802125]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1080865099021660165617969, 70853117950321663366760, -21304062729721250802125]] 
 ![![7, 0, 0], ![0, 7, 0], ![1, 0, 1]] where
  M :=![![![-1080865099021660165617969, 70853117950321663366760, -21304062729721250802125], ![2513879402107107594650750, -164790401643646381126594, 49549055220600412564635], ![-5846788516030848682626930, 383270027621289854371445, -115241346423045968561959]]]
  hmulB := by decide  
  f := ![![![-143735827153, -100522251745, -16648760050]], ![![1964553685900, 572160854997, -117171011795]], ![![1954634794951, 986054991620, 62620154736]]]
  g := ![![![-151365862327419844973692, 10121873992903094766680, -21304062729721250802125], ![352047192412358168869445, -23541485949092340160942, 49549055220600412564635], ![-818792452801114673437853, 54752861088755693481635, -115241346423045968561959]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[6, 4], [2, 1]], ![[0, 3], [4, 6]]]
 h' := ![![[2, 6], [3, 2], [0, 1]], ![[0, 1], [0, 5], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-352, -252, -44]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-44, -36, -44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143735827153, -100522251745, -16648760050]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-143735827153, -100522251745, -16648760050]] 
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![-143735827153, -100522251745, -16648760050], ![1964553685900, 572160854997, -117171011795], ![13826179391810, 7002907193085, 454989843202]]]
  hmulB := by decide  
  f := ![![![-1080865099021660165617969, 70853117950321663366760, -21304062729721250802125]], ![![-567330170288979057008152, 37189758008326228439138, -11182188736818156035445]], ![![-1761711301451544239476392, 115484105046174262081715, -34723674685910496196387]]]
  g := ![![![79898606231, -100522251745, -16648760050], ![-109340767616, 572160854997, -117171011795], ![-4417314689416, 7002907193085, 454989843202]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1080865099021660165617969, 70853117950321663366760, -21304062729721250802125]] ![![-143735827153, -100522251745, -16648760050]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 8, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 9, 10], [6, 1, 1], [0, 1]]
 g := ![![[10, 1, 5], [1, 3, 1], []], ![[3, 0, 5, 2], [5, 1, 0, 10], [7, 1]], ![[1, 5, 9, 5], [6, 3, 6, 4], [5, 1]]]
 h' := ![![[8, 9, 10], [3, 1, 4], [0, 0, 1], [0, 1]], ![[6, 1, 1], [10, 10, 3], [8, 3, 1], [8, 9, 10]], ![[0, 1], [4, 0, 4], [7, 8, 9], [6, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 3], []]
 b := ![[], [10, 1, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 8, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-681307, -378631, -44759]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61937, -34421, -4069]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6992820027, -1495790592, 649597286]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-6992820027, -1495790592, 649597286]] 
 ![![13, 0, 0], ![5, 1, 0], ![1, 0, 1]] where
  M :=![![![-6992820027, -1495790592, 649597286], ![-76652479748, -34925503325, -846193306], ![99850810108, -40266167590, -35771696631]]]
  hmulB := by decide  
  f := ![![![-1215271548153949645535, 79663760464613056292, -23953240158232153102]], ![![-249990415546027243203, 16387429305622939947, -4927360037290758640]], ![![-599162534177453555535, 39276440458586791166, -11809610861678331697]]]
  g := ![![![-12574181, -1495790592, 649597286], ![7601633091, -34925503325, -846193306], ![25919488053, -40266167590, -35771696631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53795241556297948398335, 3526398066330793511516, -1060314743915061268765]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-53795241556297948398335, 3526398066330793511516, -1060314743915061268765]] 
 ![![13, 0, 0], ![9, 1, 0], ![10, 0, 1]] where
  M :=![![![-53795241556297948398335, 3526398066330793511516, -1060314743915061268765], ![125117139781977229714270, -8201707567950313841440, 2466083322415732242751], ![-290997832045056404644618, 19075556918100743275977, -5735624245534581598689]]]
  hmulB := by decide  
  f := ![![![-278907179433, -115247044119, 2008601084]], ![![-211321503293, -107884647932, -7320079483]], ![![813312652600, 267674437031, -35263804480]]]
  g := ![![![-5763821285701882870333, 3526398066330793511516, -1060314743915061268765], ![13405513436105594758440, -8201707567950313841440, 2466083322415732242751], ![-31178584757893636780117, 19075556918100743275977, -5735624245534581598689]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 3, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![7, 3, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![9, 0, 1]] where
  M :=![![![7, 3, 0], ![0, 7, 3], ![-354, -129, 10]]]
  hmulB := by decide  
  f := ![![![457, -30, 9]], ![![305, -20, 6]], ![![507, -33, 10]]]
  g := ![![![-2, 3, 0], ![-8, 7, 3], ![75, -129, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-6992820027, -1495790592, 649597286]] ![![-53795241556297948398335, 3526398066330793511516, -1060314743915061268765]]
  ![![457, -30, 9]] where
 M := ![![![457, -30, 9]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![457, -30, 9]] ![![7, 3, 0]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [11, 3, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 6, 5], [7, 10, 12], [0, 1]]
 g := ![![[13, 9, 13], [15, 9], [0, 1], []], ![[3, 5, 2, 5], [], [15, 15], [9, 8]], ![[2, 4, 7, 3], [8, 9], [8, 2], [2, 8]]]
 h' := ![![[10, 6, 5], [5, 9, 9], [0, 6, 14], [0, 0, 1], [0, 1]], ![[7, 10, 12], [2, 14, 16], [6, 4], [1, 5, 10], [10, 6, 5]], ![[0, 1], [5, 11, 9], [12, 7, 3], [10, 12, 6], [7, 10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 1], []]
 b := ![[], [7, 3, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [11, 3, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18887, 4420, -2040]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1111, 260, -120]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3791525125, 4622626088, 1286620391]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![3791525125, 4622626088, 1286620391]] 
 ![![19, 0, 0], ![0, 19, 0], ![16, 13, 1]] where
  M :=![![![3791525125, 4622626088, 1286620391], ![-151821206138, -51533151688, 5909246479], ![-697291084522, -405918804735, -45623905209]]]
  hmulB := by decide  
  f := ![![![-249990415546027243203, 16387429305622939947, -4927360037290758640]], ![![581428484400309519520, -38113933942524621683, 11460069268332181307]], ![![116128182884441603594, -7612461394780385232, 2288909221972304125]]]
  g := ![![![-883915849, -637023105, 1286620391], ![-12966797358, -6755439785, 5909246479], ![1720599938, 9852208578, -45623905209]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [16, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 18], [0, 1]]
 g := ![![[11, 6], [2, 9], [6], [1]], ![[0, 13], [14, 10], [6], [1]]]
 h' := ![![[14, 18], [6, 5], [8, 16], [3, 14], [0, 1]], ![[0, 1], [0, 14], [4, 3], [9, 5], [14, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [5, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [16, 5, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-928, -811, -153]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![80, 62, -153]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-249990415546027243203, 16387429305622939947, -4927360037290758640]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-249990415546027243203, 16387429305622939947, -4927360037290758640]] 
 ![![19, 0, 0], ![5, 1, 0], ![13, 0, 1]] where
  M :=![![![-249990415546027243203, 16387429305622939947, -4927360037290758640], ![581428484400309519520, -38113933942524621683, 11460069268332181307], ![-1352288173663197394226, 88645505862025723319, -26653864674192440376]]]
  hmulB := by decide  
  f := ![![![3791525125, 4622626088, 1286620391]], ![![-6992820027, -1495790592, 649597286]], ![![-34105329363, -18201298189, -1520938954]]]
  g := ![![![-14098520083650635822, 16387429305622939947, -4927360037290758640], ![32790381769716540576, -38113933942524621683, 11460069268332181307], ![-76263971695201278207, 88645505862025723319, -26653864674192440376]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![3791525125, 4622626088, 1286620391]] ![![-249990415546027243203, 16387429305622939947, -4927360037290758640]]
  ![![19, 0, 0]] where
 M := ![![![19, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6697, -439, 132]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![6697, -439, 132]] 
 ![![23, 0, 0], ![7, 1, 0], ![20, 0, 1]] where
  M :=![![![6697, -439, 132], ![-15576, 1021, -307], ![36226, -2375, 714]]]
  hmulB := by decide  
  f := ![![![-131, -54, 1]], ![![-45, -24, -2]], ![![158, 47, -9]]]
  g := ![![![310, -439, 132], ![-721, 1021, -307], ![1677, -2375, 714]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12583505453974951030544714298599831, 824876848152478078392663651551700, -248023356285555868038423786203067]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-12583505453974951030544714298599831, 824876848152478078392663651551700, -248023356285555868038423786203067]] 
 ![![23, 0, 0], ![16, 1, 0], ![20, 0, 1]] where
  M :=![![![-12583505453974951030544714298599831, 824876848152478078392663651551700, -248023356285555868038423786203067], ![29266756041695592428534006771961906, -1918501133696048704892491491867950, 576853491866922210354239865348633], ![-68068712040296820821800304111138694, 4462055891417937383301692561970687, -1341647641829126494538251626519317]]]
  hmulB := by decide  
  f := ![![![-154589074306669279, -48638554390691871, 7665485925176550]], ![![-146867501220762668, -54887906058275255, 3551074188578673]], ![![75784373599887926, -5019847085543979, -16168187784836750]]]
  g := ![![![-905263821682760127132993782581117, 824876848152478078392663651551700, -248023356285555868038423786203067], ![2105465406238866413031698840646802, -1918501133696048704892491491867950, 576853491866922210354239865348633], ![-4896897976800056046254884894447102, 4462055891417937383301692561970687, -1341647641829126494538251626519317]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-513534928732681108609817, 33663359941995434927622, -10121873992903094766680]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-513534928732681108609817, 33663359941995434927622, -10121873992903094766680]] 
 ![![23, 0, 0], ![22, 1, 0], ![22, 0, 1]] where
  M :=![![![-513534928732681108609817, 33663359941995434927622, -10121873992903094766680], ![1194381131162565182468240, -78294347037848033642577, 23541485949092340160942], ![-2777895341992896138991156, 182097235351594555547734, -54752861088755693481635]]]
  hmulB := by decide  
  f := ![![![1092219832033, 382921481150, -37272405564]], ![![1235955659186, 483443732895, -20623645514]], ![![-728598026714, -88717122102, 96547366281]]]
  g := ![![![-44845548678813590963067, 33663359941995434927622, -10121873992903094766680], ![104301916309356106046270, -78294347037848033642577, 23541485949092340160942], ![-242585720685884830628058, 182097235351594555547734, -54752861088755693481635]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![6697, -439, 132]] ![![-12583505453974951030544714298599831, 824876848152478078392663651551700, -248023356285555868038423786203067]]
  ![![-106104911916893792476162020773284652549, 6955413627436878807039295657551895634, -2091348588695391195877884611790539430]] where
 M := ![![![-106104911916893792476162020773284652549, 6955413627436878807039295657551895634, -2091348588695391195877884611790539430]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-106104911916893792476162020773284652549, 6955413627436878807039295657551895634, -2091348588695391195877884611790539430]] ![![-513534928732681108609817, 33663359941995434927622, -10121873992903094766680]]
  ![![23, 0, 0]] where
 M := ![![![68605540678491384631459267043515520552513130059044371494418773, -4497246205968326760542924810351052004796057101156512569768916, 1352228639396315621286029629674927854236228015458736217762598]]]
 hmul := by decide  
 g := ![![![![2982849594717016723106924654065892197935353480828016151931251, -195532443737753337414909774363089217599828569615500546511692, 58792549538970244403740418681518602358096870237336357294026]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [15, 19, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 0, 26], [9, 28, 3], [0, 1]]
 g := ![![[18, 22, 13], [5, 13], [13], [1]], ![[26, 21, 5, 27], [25, 5], [16, 27, 0, 26], [28, 9, 0, 2]], ![[11, 24, 24, 26], [20, 6], [12, 26, 26, 3], [3, 0, 2, 27]]]
 h' := ![![[20, 0, 26], [18, 25, 19], [8, 7, 19], [14, 10], [0, 1]], ![[9, 28, 3], [27, 16, 22], [5, 16, 18], [11, 0, 28], [20, 0, 26]], ![[0, 1], [12, 17, 17], [14, 6, 21], [17, 19, 1], [9, 28, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20], []]
 b := ![[], [1, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [15, 19, 0, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-330339, -140534, 9454]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11391, -4846, 326]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4947709701757, 12638674609155, 4519454904298]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![4947709701757, 12638674609155, 4519454904298]] 
 ![![31, 0, 0], ![0, 31, 0], ![23, 6, 1]] where
  M :=![![![4947709701757, 12638674609155, 4519454904298], ![-533295678707164, -189388851183057, 17158129513453], ![-2024659282587454, -1271095247785643, -172230721669604]]]
  hmulB := by decide  
  f := ![![![1755748238737930245319530797, -115093212985569027652895774, 34606141552287177519469071]], ![![-4083524703169886947297350378, 267684151989581611982360744, -80487071433281850133426703]], ![![818662441970333299171272807, -53665148976431140505885177, 16135997021264959483747176]]]
  g := ![![![-3193540422487, -467034026343, 4519454904298], ![-29933311532793, -9430246073025, 17158129513453], ![62472494058498, -7668094121549, -172230721669604]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [1, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 30], [0, 1]]
 g := ![![[9, 1], [22, 7], [12, 14], [22, 1]], ![[0, 30], [21, 24], [10, 17], [13, 30]]]
 h' := ![![[22, 30], [9, 1], [19, 21], [9, 18], [0, 1]], ![[0, 1], [0, 30], [16, 10], [2, 13], [22, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [18, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [1, 9, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![405, -110, -8]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, -2, -8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7721573085906611, -6249351667583384, -4114411736597877]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![7721573085906611, -6249351667583384, -4114411736597877]] 
 ![![31, 0, 0], ![24, 1, 0], ![13, 0, 1]] where
  M :=![![![7721573085906611, -6249351667583384, -4114411736597877], ![485500584918549486, 184641277759615322, -10363763404181261], ![1222924081693388798, 931142411298343709, 174277514355434061]]]
  hmulB := by decide  
  f := ![![![41828962581651917558560738211319691, -2741981790530533992057528434463369, 824457042386949652855601489638618]], ![![29245457127676966528016023912719860, -1917104942378055913664864782911669, 576433686101393784817177703435551]], ![![24840143027174770331842483104402471, -1628326777689770140258902799932788, 489604082641930439796476341204400]]]
  g := ![![![6812689215602588, -6249351667583384, -4114411736597877], ![-122940682485737479, 184641277759615322, -10363763404181261], ![-754519402454435581, 931142411298343709, 174277514355434061]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![4947709701757, 12638674609155, 4519454904298]] ![![7721573085906611, -6249351667583384, -4114411736597877]]
  ![![31, 0, 0]] where
 M := ![![![11701238256003252192775736013661, 6510957188489157299650436028504, 636298218704627891697545079834]]]
 hmul := by decide  
 g := ![![![![377459298580750070734701161731, 210030877048037332246788258984, 20525748990471867474114357414]]]]
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


lemma PB251I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB251I0 : PrimesBelowBoundCertificateInterval O 1 31 251 where
  m := 11
  g := ![2, 1, 2, 2, 1, 3, 1, 2, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB251I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0]
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
    · exact ![4, 2]
    · exact ![27]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![24389]
    · exact ![961, 31]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I13N0, I13N1, I13N2, I19N1, I23N0, I23N1, I23N2, I31N1]
  Il := ![[I2N0, I2N1], [I3N0], [I5N0, I5N1], [I7N0, I7N1], [], [I13N0, I13N1, I13N2], [], [I19N1], [I23N0, I23N1, I23N2], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
