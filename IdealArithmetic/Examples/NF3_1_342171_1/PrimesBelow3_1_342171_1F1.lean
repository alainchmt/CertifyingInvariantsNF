
import IdealArithmetic.Examples.NF3_1_342171_1.RI3_1_342171_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5086, 6169, -12897]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![5086, 6169, -12897]] 
 ![![37, 0, 0], ![0, 37, 0], ![8, 4, 1]] where
  M :=![![![5086, 6169, -12897], ![-1238671, 204710, 56080], ![1011097, -298887, 192372]]]
  hmulB := by decide  
  f := ![![![1517352840, 72108183, 80705470]], ![![7972646956, 378878973, 424051811]], ![![1309225115, 62217463, 69635503]]]
  g := ![![![2926, 1561, -12897], ![-45603, -530, 56080], ![-14267, -28875, 192372]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [32, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 36], [0, 1]]
 g := ![![[7, 16], [21], [19, 7], [4], [1]], ![[12, 21], [21], [5, 30], [4], [1]]]
 h' := ![![[35, 36], [28, 4], [21, 24], [8, 9], [5, 35], [0, 1]], ![[0, 1], [20, 33], [10, 13], [27, 28], [9, 2], [35, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [3, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [32, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1188, 372, -721]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![188, 88, -721]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1517352840, 72108183, 80705470]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![1517352840, 72108183, 80705470]] 
 ![![37, 0, 0], ![10, 1, 0], ![11, 0, 1]] where
  M :=![![![1517352840, 72108183, 80705470], ![7972646956, 378878973, 424051811], ![4411918711, 209664775, 234662607]]]
  hmulB := by decide  
  f := ![![![5086, 6169, -12897]], ![![-32103, 7200, -1970]], ![![28839, -6244, 1365]]]
  g := ![![![-2472680, 72108183, 80705470], ![-12992235, 378878973, 424051811], ![-7189668, 209664775, 234662607]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![5086, 6169, -12897]] ![![1517352840, 72108183, 80705470]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73556573986357904, -3495581751349409, -3912351642060440]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-73556573986357904, -3495581751349409, -3912351642060440]] 
 ![![41, 0, 0], ![0, 41, 0], ![24, 40, 1]] where
  M :=![![![-73556573986357904, -3495581751349409, -3912351642060440], ![-386489272782561498, -18366881106800713, -20556720617385423], ![-213876177334958593, -10163900002725905, -11375717604101895]]]
  hmulB := by decide  
  f := ![![![119532480, -23894345, 2068993]], ![![152903631, 64603240, -169329408]], ![![160999159, 58589863, -161247038]]]
  g := ![![![496094278612016, 3731670339782151, -3912351642060440], ![2606634683772894, 19607364477771127, -20556720617385423], ![1442464516182607, 10850361077106095, -11375717604101895]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [6, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 40], [0, 1]]
 g := ![![[9, 37], [39], [21], [9, 5], [1]], ![[20, 4], [39], [21], [26, 36], [1]]]
 h' := ![![[28, 40], [16, 23], [2, 30], [28, 12], [35, 28], [0, 1]], ![[0, 1], [4, 18], [22, 11], [36, 29], [40, 13], [28, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [5, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [6, 13, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10272, 5184, -4446]
  a := ![5, 0, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2352, 4464, -4446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![119532480, -23894345, 2068993]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![119532480, -23894345, 2068993]] 
 ![![41, 0, 0], ![8, 1, 0], ![31, 0, 1]] where
  M :=![![![119532480, -23894345, 2068993], ![152903631, 64603240, -169329408], ![-2383959241, 391519063, 112391930]]]
  hmulB := by decide  
  f := ![![![-73556573986357904, -3495581751349409, -3912351642060440]], ![![-23779069870083530, -1130037441892585, -1264769115948023]], ![![-60832438314928137, -2890900836452624, -3235576061170135]]]
  g := ![![![6013377, -23894345, 2068993], ![119153399, 64603240, -169329408], ![-219518575, 391519063, 112391930]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-73556573986357904, -3495581751349409, -3912351642060440]] ![![119532480, -23894345, 2068993]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [29, 3, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 19, 8], [34, 23, 35], [0, 1]]
 g := ![![[29, 12, 21], [1, 3, 9], [30, 21], [11, 10, 1], []], ![[20, 20, 24, 8], [34, 42, 23, 42], [25, 21], [41, 8, 15, 18], [41, 21]], ![[40, 7, 3, 38], [11, 41, 26, 35], [24, 41], [7, 40, 33, 36], [14, 21]]]
 h' := ![![[19, 19, 8], [14, 36, 8], [13, 7, 3], [25, 21, 8], [0, 0, 1], [0, 1]], ![[34, 23, 35], [8, 2, 42], [27, 17, 39], [35, 18, 8], [32, 33, 23], [19, 19, 8]], ![[0, 1], [14, 5, 36], [7, 19, 1], [31, 4, 27], [19, 10, 19], [34, 23, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 17], []]
 b := ![[], [3, 0, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [29, 3, 33, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5261797469, 1940384976, -2010434169]
  a := ![-66, -64, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-122367383, 45125232, -46754283]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-48803, -3226, 22614]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-48803, -3226, 22614]] 
 ![![47, 0, 0], ![2, 1, 0], ![33, 0, 1]] where
  M :=![![![-48803, -3226, 22614], ![2187106, -391239, -45196], ![-1036570, 410214, -384787]]]
  hmulB := by decide  
  f := ![![![-169083713037, -8035256534, -8993281042]], ![![-26097578728, -1240218447, -1388086740]], ![![-129178668525, -6138874772, -6870798197]]]
  g := ![![![-16779, -3226, 22614], ![94916, -391239, -45196], ![230659, 410214, -384787]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2545356948208374477864094, -120961360985597060229703, -135383296098046873998484]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-2545356948208374477864094, -120961360985597060229703, -135383296098046873998484]] 
 ![![47, 0, 0], ![5, 1, 0], ![43, 0, 1]] where
  M :=![![![-2545356948208374477864094, -120961360985597060229703, -135383296098046873998484], ![-13374102443481740898312354, -635568867723268428116537, -711346230801132547609437], ![-7400986540465414874329703, -351712322784794080530199, -393646145752074307657131]]]
  hmulB := by decide  
  f := ![![![391428812616, -395216256223, 579562822697]], ![![1220942667069, -227091724791, -9537500059]], ![![-852139324201, -38150000236, 362008597965]]]
  g := ![![![82573012530545242664239, -120961360985597060229703, -135383296098046873998484], ![433864464246453208286726, -635568867723268428116537, -711346230801132547609437], ![240092751931867037395275, -351712322784794080530199, -393646145752074307657131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4890988, 274245, 1186535]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-4890988, 274245, 1186535]] 
 ![![47, 0, 0], ![40, 1, 0], ![1, 0, 1]] where
  M :=![![![-4890988, 274245, 1186535], ![115642385, -22414768, 733180], ![-11367355, 14870885, -22963258]]]
  hmulB := by decide  
  f := ![![![-503813065129844, -23942384223685, -26796977697980]], ![![-485100302347770, -23053109634707, -25801677016745]], ![![-41887681882807, -1990601362470, -2227936024137]]]
  g := ![![![-362709, 274245, 1186535], ![21521275, -22414768, 733180], ![-12409351, 14870885, -22963258]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-48803, -3226, 22614]] ![![-2545356948208374477864094, -120961360985597060229703, -135383296098046873998484]]
  ![![503813065129844, 23942384223685, 26796977697980]] where
 M := ![![![503813065129844, 23942384223685, 26796977697980]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![503813065129844, 23942384223685, 26796977697980]] ![![-4890988, 274245, 1186535]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![120600660, -25807389, 5158628]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![120600660, -25807389, 5158628]] 
 ![![53, 0, 0], ![0, 53, 0], ![40, 35, 1]] where
  M :=![![![120600660, -25807389, 5158628], ![448772138, 17413851, -185810351], ![-2668392829, 469648883, 69028629]]]
  hmulB := by decide  
  f := ![![![-1669201472776004, -79324387900985, -88782045832587]], ![![-8770507221562909, -416795173188184, -466488669474308]], ![![-7143193430669712, -339461386649669, -379934559665858]]]
  g := ![![![-1617820, -3893573, 5158628], ![148701626, 123033512, -185810351], ![-102444113, -36723644, 69028629]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [35, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 52], [0, 1]]
 g := ![![[33, 47], [17], [20, 7], [29], [11, 1]], ![[20, 6], [17], [44, 46], [29], [22, 52]]]
 h' := ![![[11, 52], [3, 43], [42, 21], [29, 31], [39, 33], [0, 1]], ![[0, 1], [52, 10], [8, 32], [52, 22], [31, 20], [11, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [5, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [35, 42, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7024, 4613, -5465]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3992, 3696, -5465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1669201472776004, -79324387900985, -88782045832587]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-1669201472776004, -79324387900985, -88782045832587]] 
 ![![53, 0, 0], ![21, 1, 0], ![10, 0, 1]] where
  M :=![![![-1669201472776004, -79324387900985, -88782045832587], ![-8770507221562909, -416795173188184, -466488669474308], ![-4853440159752761, -230646914806617, -258146397386214]]]
  hmulB := by decide  
  f := ![![![120600660, -25807389, 5158628]], ![![56252566, -9897006, -1461871]], ![![-27592193, 3991981, 2275753]]]
  g := ![![![16687379839067, -79324387900985, -88782045832587], ![87680719059095, -416795173188184, -466488669474308], ![48520925000912, -230646914806617, -258146397386214]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![120600660, -25807389, 5158628]] ![![-1669201472776004, -79324387900985, -88782045832587]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [13, 26, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 41, 16], [25, 17, 43], [0, 1]]
 g := ![![[18, 26, 25], [52, 9, 7], [], [16, 48, 21], [1]], ![[24, 39, 34, 19], [21, 26, 56, 46], [24, 26], [33, 30, 46, 25], [51, 16, 8, 25]], ![[39, 30, 28, 23], [2, 38, 51, 47], [42, 26], [11, 14, 41, 11], [42, 12, 50, 34]]]
 h' := ![![[2, 41, 16], [32, 0, 5], [17, 17, 19], [28, 14], [46, 33, 27], [0, 1]], ![[25, 17, 43], [32, 11, 26], [51, 19, 5], [56, 43, 47], [53, 20, 43], [2, 41, 16]], ![[0, 1], [54, 48, 28], [30, 23, 35], [24, 2, 12], [34, 6, 48], [25, 17, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 17], []]
 b := ![[], [8, 10, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [13, 26, 32, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-243257, 105610, -107793]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4123, 1790, -1827]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [54, 49, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 47, 24], [57, 13, 37], [0, 1]]
 g := ![![[20, 6, 56], [52, 19], [5, 47, 41], [1, 30, 13], [1]], ![[40, 40, 12, 21], [28, 39], [25, 46, 13, 54], [24, 36, 51, 29], [53, 34, 8, 38]], ![[21, 29, 14, 8], [40, 52], [7, 13, 12, 51], [19, 9, 16, 43], [16, 19, 33, 23]]]
 h' := ![![[18, 47, 24], [3, 2, 19], [35, 11, 18], [7, 27, 23], [7, 12, 14], [0, 1]], ![[57, 13, 37], [33, 33, 51], [9, 29, 10], [17, 49, 32], [42, 15, 43], [18, 47, 24]], ![[0, 1], [33, 26, 52], [27, 21, 33], [6, 46, 6], [48, 34, 4], [57, 13, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 16], []]
 b := ![[], [29, 4, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [54, 49, 47, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-154086, 944402, -329888]
  a := ![3, 21, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2526, 15482, -5408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-214778376, 29748559, 20109124]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-214778376, 29748559, 20109124]] 
 ![![67, 0, 0], ![31, 1, 0], ![50, 0, 1]] where
  M :=![![![-214778376, 29748559, 20109124], ![2010082146, -486666677, 188130789], ![2242118255, -124482401, -546163795]]]
  hmulB := by decide  
  f := ![![![289218691527103604, 13744353841694681, 15383060430743999]], ![![156498880698593567, 7437195641793633, 8323914773346011]], ![![228386253212175467, 10853453005242057, 12147484369573864]]]
  g := ![![![-31976715, 29748559, 20109124], ![114779249, -486666677, 188130789], ![498645708, -124482401, -546163795]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18, 1, 1]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![18, 1, 1]] 
 ![![67, 0, 0], ![38, 1, 0], ![47, 0, 1]] where
  M :=![![![18, 1, 1], ![99, 4, 6], ![65, 1, 2]]]
  hmulB := by decide  
  f := ![![![2, -1, 2]], ![![4, -1, 1]], ![![-1, 0, 1]]]
  g := ![![![-1, 1, 1], ![-5, 4, 6], ![-1, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11054934198653763, -525356526995800, -587993535057718]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![-11054934198653763, -525356526995800, -587993535057718]] 
 ![![67, 0, 0], ![65, 1, 0], ![0, 0, 1]] where
  M :=![![![-11054934198653763, -525356526995800, -587993535057718], ![-58086085954590246, -2760387699783793, -3089502153912882], ![-32143789996745624, -1527548655986488, -1709674645792193]]]
  hmulB := by decide  
  f := ![![![-386189633, 75675016, -3931226]], ![![-378094105, 69661639, 4151144]], ![![111436952, -17880968, -6013377]]]
  g := ![![![344675224717511, -525356526995800, -587993535057718], ![1811031560169497, -2760387699783793, -3089502153912882], ![1002192128990688, -1527548655986488, -1709674645792193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-214778376, 29748559, 20109124]] ![![18, 1, 1]]
  ![![386189633, -75675016, 3931226]] where
 M := ![![![386189633, -75675016, 3931226]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![386189633, -75675016, 3931226]] ![![-11054934198653763, -525356526995800, -587993535057718]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14250606463415, 677222404464, 757966019568]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![14250606463415, 677222404464, 757966019568]] 
 ![![71, 0, 0], ![20, 1, 0], ![62, 0, 1]] where
  M :=![![![14250606463415, 677222404464, 757966019568], ![74877148707024, 3558338574359, 3982590811680], ![41435660606832, 1969120246128, 2203893765431]]]
  hmulB := by decide  
  f := ![![![8689, 948720, -1717392]], ![![-2317124, 643559, -366048]], ![![2077762, 241008, -1150105]]]
  g := ![![![-651939927311, 677222404464, 757966019568], ![-3425496522596, 3558338574359, 3982590811680], ![-1895607855950, 1969120246128, 2203893765431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3887407873, 599758976, 253155798]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-3887407873, 599758976, 253155798]] 
 ![![71, 0, 0], ![23, 1, 0], ![33, 0, 1]] where
  M :=![![![-3887407873, 599758976, 253155798], ![25755630358, -7084985867, 3945157034], ![50075635136, -4945891872, -8284503819]]]
  hmulB := by decide  
  f := ![![![78207912580946753721, 3716624323473655488, 4159748593850144050]], ![![31122688050875867879, 1479023485022004573, 1655363934211531796]], ![![39552981965422293599, 1879650920058142304, 2103757224602474523]]]
  g := ![![![-366704305, 599758976, 253155798], ![824227087, -7084985867, 3945157034], ![6158024989, -4945891872, -8284503819]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3907887, 185712, 207854]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![3907887, 185712, 207854]] 
 ![![71, 0, 0], ![28, 1, 0], ![6, 0, 1]] where
  M :=![![![3907887, 185712, 207854], ![20533262, 975789, 1092130], ![11362736, 539984, 604365]]]
  hmulB := by decide  
  f := ![![![-6935, 1456, -246]], ![![-3030, 549, 50]], ![![1514, -240, -87]]]
  g := ![![![-35763, 185712, 207854], ![-187910, 975789, 1092130], ![-103986, 539984, 604365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![14250606463415, 677222404464, 757966019568]] ![![-3887407873, 599758976, 253155798]]
  ![![-6935, 1456, -246]] where
 M := ![![![-6935, 1456, -246]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![-6935, 1456, -246]] ![![3907887, 185712, 207854]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7261340209, 345076000, 386218590]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![7261340209, 345076000, 386218590]] 
 ![![73, 0, 0], ![0, 73, 0], ![50, 30, 1]] where
  M :=![![![7261340209, 345076000, 386218590], ![38153355230, 1813137359, 2029313410], ![21113377120, 1003357440, 1122985359]]]
  hmulB := by decide  
  f := ![![![-32103, 7200, -1970]], ![![-176690, 4647, 52370]], ![![-84170, 4930, 20039]]]
  g := ![![![-165062867, -153992900, 386218590], ![-867291990, -809126917, 2029313410], ![-479943710, -447756210, 1122985359]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [41, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 72], [0, 1]]
 g := ![![[43, 57], [9], [67], [2, 8], [48], [1]], ![[0, 16], [9], [67], [60, 65], [48], [1]]]
 h' := ![![[62, 72], [53, 38], [35, 3], [64, 40], [5, 9], [32, 62], [0, 1]], ![[0, 1], [0, 35], [2, 70], [62, 33], [52, 64], [7, 11], [62, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [41, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [41, 11, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5121, 1906, -1523]
  a := ![-3, 1, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![973, 652, -1523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32103, 7200, -1970]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-32103, 7200, -1970]] 
 ![![73, 0, 0], ![10, 1, 0], ![68, 0, 1]] where
  M :=![![![-32103, 7200, -1970], ![-176690, 4647, 52370], ![761440, -139520, -9753]]]
  hmulB := by decide  
  f := ![![![7261340209, 345076000, 386218590]], ![![1517352840, 72108183, 80705470]], ![![7053212484, 335185280, 375148623]]]
  g := ![![![409, 7200, -1970], ![-51840, 4647, 52370], ![38628, -139520, -9753]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![7261340209, 345076000, 386218590]] ![![-32103, 7200, -1970]]
  ![![73, 0, 0]] where
 M := ![![![73, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105956, -11665, 57520]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-105956, -11665, 57520]] 
 ![![79, 0, 0], ![0, 79, 0], ![67, 33, 1]] where
  M :=![![![-105956, -11665, 57520], ![5556110, -980421, -139175], ![-2972145, 1095295, -957091]]]
  hmulB := by decide  
  f := ![![![-13807465784, -656163315, -734396105]], ![![-72548748815, -3447687524, -3858747100]], ![![-42523494742, -2020816688, -2261753851]]]
  g := ![![![-50124, -24175, 57520], ![188365, 45726, -139175], ![774088, 413662, -957091]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [12, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 78], [0, 1]]
 g := ![![[35, 20], [41, 5], [54, 26], [17, 67], [72], [1]], ![[9, 59], [74, 74], [36, 53], [1, 12], [72], [1]]]
 h' := ![![[54, 78], [61, 40], [63, 59], [33, 37], [70, 64], [67, 54], [0, 1]], ![[0, 1], [9, 39], [10, 20], [56, 42], [50, 15], [60, 25], [54, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [22, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [12, 25, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2022, 1984, -2499]
  a := ![4, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2145, 1069, -2499]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13807465784, -656163315, -734396105]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-13807465784, -656163315, -734396105]] 
 ![![79, 0, 0], ![7, 1, 0], ![60, 0, 1]] where
  M :=![![![-13807465784, -656163315, -734396105], ![-72548748815, -3447687524, -3858747100], ![-40147166195, -1907887955, -2135360894]]]
  hmulB := by decide  
  f := ![![![-105956, -11665, 57520]], ![![60942, -13444, 3335]], ![![-118095, 5005, 31571]]]
  g := ![![![441132199, -656163315, -734396105], ![2317846707, -3447687524, -3858747100], ![1282654470, -1907887955, -2135360894]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-105956, -11665, 57520]] ![![-13807465784, -656163315, -734396105]]
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


lemma PB166I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB166I1 : PrimesBelowBoundCertificateInterval O 31 79 166 where
  m := 11
  g := ![2, 2, 1, 3, 2, 1, 1, 3, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB166I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
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
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
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
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N1, I47N0, I47N1, I47N2, I53N1, I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [], [I47N0, I47N1, I47N2], [I53N1], [], [], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
