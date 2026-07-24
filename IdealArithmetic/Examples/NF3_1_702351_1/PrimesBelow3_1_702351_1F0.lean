
import IdealArithmetic.Examples.NF3_1_702351_1.RI3_1_702351_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 1]], ![[0, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 1, 1], [0, 0, 1]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1292742, -13598, -23842]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-646371, -6799, -11921]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9743104122904, -1024644587309, -623221726641]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-9743104122904, -1024644587309, -623221726641]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![-9743104122904, -1024644587309, -623221726641], ![-102387987163819, -10767748710213, -6549290384522], ![-136299579131263, -14334099712743, -8718459535595]]]
  hmulB := by decide  
  f := ![![![-167889, 477592, -346765]], ![![-18403253, 421629, 998793]], ![![30835908, -2340137, -446337]]]
  g := ![![![-2149123831668, -1024644587309, -623221726641], ![-22584636324783, -10767748710213, -6549290384522], ![-30064820211529, -14334099712743, -8718459535595]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-9743104122904, -1024644587309, -623221726641]] ![![-9743104122904, -1024644587309, -623221726641]]
  ![![284784233849246769411843870, 29949656709364756483398416, 18216342522957830265603157]] where
 M := ![![![284784233849246769411843870, 29949656709364756483398416, 18216342522957830265603157]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![284784233849246769411843870, 29949656709364756483398416, 18216342522957830265603157]] ![![-9743104122904, -1024644587309, -623221726641]]
  ![![3, 0, 0]] where
 M := ![![![-8324047328863959219149408534872946306475, -875407871293713613680057134411232598089, -532451165818985668000871160811663131237]]]
 hmul := by decide  
 g := ![![![![-2774682442954653073049802844957648768825, -291802623764571204560019044803744199363, -177483721939661889333623720270554377079]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [4, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 1], [1, 3, 4], [0, 1]]
 g := ![![[4, 0, 1], []], ![[0, 1, 1, 4], [2, 1]], ![[0, 1, 2, 4], [4, 1]]]
 h' := ![![[4, 1, 1], [0, 0, 1], [0, 1]], ![[1, 3, 4], [3, 2, 3], [4, 1, 1]], ![[0, 1], [0, 3, 1], [1, 3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 4], []]
 b := ![[], [2, 3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [4, 1, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21372470, 111780, -401040]
  a := ![5, 0, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4274494, 22356, -80208]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1685858997911678417, 177295272162349688, 107836675283177055]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![1685858997911678417, 177295272162349688, 107836675283177055]] 
 ![![7, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![1685858997911678417, 177295272162349688, 107836675283177055], ![17716295264916205231, 1863154270074028105, 1133230229853270761], ![23584051755112155238, 2480243531513072265, 1508563725749328729]]]
  hmulB := by decide  
  f := ![![![2825384880, -357706977, 66741793]], ![![1836485657, 301424418, -357706977]], ![![-8262222985, 168193466, 464261950]]]
  g := ![![![200103864352307382, 177295272162349688, 107836675283177055], ![2102844394998415195, 1863154270074028105, 1133230229853270761], ![2799320642549964892, 2480243531513072265, 1508563725749328729]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28055201, 12911264, -7693447]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-28055201, 12911264, -7693447]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![-28055201, 12911264, -7693447], ![-1212822439, -15143937, 98072295], ![2432612066, -176949281, -40966465]]]
  hmulB := by decide  
  f := ![![![-17974215651342600, -1890278759823367, -1149728215150041]], ![![-29551573687163705, -3107824738712762, -1890278759823367]], ![![-51327525191816543, -5397917358198735, -3283186597488497]]]
  g := ![![![742031, 12911264, -7693447], ![-255158896, -15143937, 98072295], ![407908591, -176949281, -40966465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 0, 1]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-14, 0, 1]] 
 ![![7, 0, 0], ![5, 1, 0], ![0, 0, 1]] where
  M :=![![![-14, 0, 1], ![161, -14, -1], ![-46, 23, -14]]]
  hmulB := by decide  
  f := ![![![-219, -23, -14]], ![![-485, -51, -31]], ![![-437, -46, -28]]]
  g := ![![![-2, 0, 1], ![33, -14, -1], ![-23, 23, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![1685858997911678417, 177295272162349688, 107836675283177055]] ![![-28055201, 12911264, -7693447]]
  ![![-219, -23, -14]] where
 M := ![![![-219, -23, -14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-219, -23, -14]] ![![-14, 0, 1]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3801735853310238, -399813859662606, -243179622515089]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-3801735853310238, -399813859662606, -243179622515089]] 
 ![![11, 0, 0], ![0, 11, 0], ![9, 10, 1]] where
  M :=![![![-3801735853310238, -399813859662606, -243179622515089], ![-39951546944254541, -4201549712972844, -2555517395123153], ![-53183768769985472, -5593131317847047, -3401921993647632]]]
  hmulB := by decide  
  f := ![![![-67138747, 1750619, 3484218]], ![![564460336, -65388128, 8770115]], ![![469266388, -50726245, 4560886]]]
  g := ![![![-146647204606767, 184725669589844, -243179622515089], ![-1541080944376924, 1941238567114426, -2555517395123153], ![-2051497347923344, 2584189874420843, -3401921993647632]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[8, 9], [2, 5], [1]], ![[0, 2], [0, 6], [1]]]
 h' := ![![[4, 10], [1, 8], [6, 4], [0, 1]], ![[0, 1], [0, 3], [0, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [10, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [5, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2291437, 922919, 28075]
  a := ![-66, -64, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![185342, 58379, 28075]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67138747, 1750619, 3484218]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-67138747, 1750619, 3484218]] 
 ![![11, 0, 0], ![8, 1, 0], ![1, 0, 1]] where
  M :=![![![-67138747, 1750619, 3484218], ![564460336, -65388128, 8770115], ![121575631, 80137014, -68889366]]]
  hmulB := by decide  
  f := ![![![-3801735853310238, -399813859662606, -243179622515089]], ![![-6396857615521495, -672732780933972, -409177670476715]], ![![-5180500420299610, -544813197955423, -331372874196611]]]
  g := ![![![-7693447, 1750619, 3484218], ![98072295, -65388128, 8770115], ![-40966465, 80137014, -68889366]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-3801735853310238, -399813859662606, -243179622515089]] ![![-67138747, 1750619, 3484218]]
  ![![11, 0, 0]] where
 M := ![![![11, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21315271463487371466, -2241644680850909971, -1363440246324372048]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-21315271463487371466, -2241644680850909971, -1363440246324372048]] 
 ![![13, 0, 0], ![2, 1, 0], ![5, 0, 1]] where
  M :=![![![-21315271463487371466, -2241644680850909971, -1363440246324372048], ![-223997169019925719670, -23556916144338281437, -14328072519631997749], ![-298186542286075391123, -31359125665460557104, -19073626782636461495]]]
  hmulB := by decide  
  f := ![![![-9109809419, -792362347, 1246417697]], ![![13912992745, -883607420, -330778364]], ![![-17727276848, 1900445792, -160412199]]]
  g := ![![![-770367759243360868, -2241644680850909971, -1363440246324372048], ![-8095613394853012927, -23556916144338281437, -14328072519631997749], ![-10776935157074766880, -31359125665460557104, -19073626782636461495]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97179, -749, -6384]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![97179, -749, -6384]] 
 ![![13, 0, 0], ![12, 1, 0], ![4, 0, 1]] where
  M :=![![![97179, -749, -6384], ![-1029322, 96430, 1141], ![173075, -146832, 97928]]]
  hmulB := by decide  
  f := ![![![9610732352, 1010723560, 614754511]], ![![16640439355, 1750010664, 1064412657]], ![![13299285774, 1398634461, 850694372]]]
  g := ![![![10131, -749, -6384], ![-168542, 96430, 1141], ![118719, -146832, 97928]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-21315271463487371466, -2241644680850909971, -1363440246324372048]] ![![97179, -749, -6384]]
  ![![-9610732352, -1010723560, -614754511]] where
 M := ![![![-9610732352, -1010723560, -614754511]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-9610732352, -1010723560, -614754511]] ![![97179, -749, -6384]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N1
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [11, 15, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 16, 6], [11, 0, 11], [0, 1]]
 g := ![![[7, 9, 9], [5, 2], [2, 1], []], ![[2, 12, 1, 10], [15, 13], [], [9, 2]], ![[2, 14, 8, 5], [12, 4], [13, 1], [4, 2]]]
 h' := ![![[8, 16, 6], [4, 7, 3], [12, 10, 6], [0, 0, 1], [0, 1]], ![[11, 0, 11], [6, 1, 8], [1, 6, 9], [16, 14], [8, 16, 6]], ![[0, 1], [6, 9, 6], [6, 1, 2], [9, 3, 16], [11, 0, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 11], []]
 b := ![[], [8, 15, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [11, 15, 15, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21632857, 13719, 246942]
  a := ![-5, -1, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1272521, 807, 14526]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-922, -97, -59]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-922, -97, -59]] 
 ![![19, 0, 0], ![0, 19, 0], ![5, 1, 1]] where
  M :=![![![-922, -97, -59], ![-9693, -1019, -620], ![-12903, -1357, -825]]]
  hmulB := by decide  
  f := ![![![35, -2, -1]], ![![-165, 33, -13]], ![![-14, 0, 1]]]
  g := ![![![-33, -2, -59], ![-347, -21, -620], ![-462, -28, -825]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [12, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 18], [0, 1]]
 g := ![![[16, 1], [15, 4], [4], [1]], ![[14, 18], [7, 15], [4], [1]]]
 h' := ![![[17, 18], [10, 18], [1, 2], [7, 17], [0, 1]], ![[0, 1], [12, 1], [16, 17], [11, 2], [17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [13, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [12, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2274, 1135, 14]
  a := ![-2, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![116, 59, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, -2, -1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![35, -2, -1]] 
 ![![19, 0, 0], ![13, 1, 0], ![15, 0, 1]] where
  M :=![![![35, -2, -1], ![-165, 33, -13], ![-276, -23, 37]]]
  hmulB := by decide  
  f := ![![![-922, -97, -59]], ![![-1141, -120, -73]], ![![-1407, -148, -90]]]
  g := ![![![4, -2, -1], ![-21, 33, -13], ![-28, -23, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-922, -97, -59]] ![![35, -2, -1]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 2, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-21, 2, 0]] 
 ![![23, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![-21, 2, 0], ![4, -19, 14], ![322, 0, -23]]]
  hmulB := by decide  
  f := ![![![437, 46, 28]], ![![219, 23, 14]], ![![266, 28, 17]]]
  g := ![![![-1, 2, 0], ![1, -19, 14], ![14, 0, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24951, 2624, 1596]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![24951, 2624, 1596]] 
 ![![23, 0, 0], ![21, 1, 0], ![0, 0, 1]] where
  M :=![![![24951, 2624, 1596], ![262204, 27575, 16772], ![349048, 36708, 22327]]]
  hmulB := by decide  
  f := ![![![449, -80, 28]], ![![599, -57, 0]], ![![-616, 28, 23]]]
  g := ![![![-1311, 2624, 1596], ![-13777, 27575, 16772], ![-18340, 36708, 22327]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-21, 2, 0]] ![![-21, 2, 0]]
  ![![449, -80, 28]] where
 M := ![![![449, -80, 28]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![449, -80, 28]] ![![24951, 2624, 1596]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18569362, 1952868, 1187797]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![18569362, 1952868, 1187797]] 
 ![![29, 0, 0], ![2, 1, 0], ![16, 0, 1]] where
  M :=![![![18569362, 1952868, 1187797], ![195141053, 20522230, 12482279], ![259773086, 27319331, 16616494]]]
  hmulB := by decide  
  f := ![![![26271, -985, -1138]], ![![-4574, 804, -277]], ![![10831, -1446, 312]]]
  g := ![![![-149694, 1952868, 1187797], ![-1573099, 20522230, 12482279], ![-2094120, 27319331, 16616494]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, 6, 5]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-133, 6, 5]] 
 ![![29, 0, 0], ![28, 1, 0], ![21, 0, 1]] where
  M :=![![![-133, 6, 5], ![817, -127, 37], ![736, 115, -139]]]
  hmulB := by decide  
  f := ![![![-13398, -1409, -857]], ![![-17791, -1871, -1138]], ![![-16165, -1700, -1034]]]
  g := ![![![-14, 6, 5], ![124, -127, 37], ![15, 115, -139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![18569362, 1952868, 1187797]] ![![-133, 6, 5]]
  ![![-13398, -1409, -857]] where
 M := ![![![-13398, -1409, -857]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-13398, -1409, -857]] ![![-133, 6, 5]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![915, -131, 33]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![915, -131, 33]] 
 ![![31, 0, 0], ![3, 1, 0], ![3, 0, 1]] where
  M :=![![![915, -131, 33], ![5051, 784, -950], ![-22609, 759, 1046]]]
  hmulB := by decide  
  f := ![![![1541114, 162073, 98578]], ![![671566, 70626, 42957]], ![![844597, 88823, 54025]]]
  g := ![![![39, -131, 33], ![179, 784, -950], ![-904, 759, 1046]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1560759866244, -164139080201, -99834657050]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-1560759866244, -164139080201, -99834657050]] 
 ![![31, 0, 0], ![12, 1, 0], ![9, 0, 1]] where
  M :=![![![-1560759866244, -164139080201, -99834657050], ![-16401657945452, -1724898946445, -1049138904357], ![-21833997688061, -2296197112150, -1396620786043]]]
  hmulB := by decide  
  f := ![![![-7829585, 277143, 351493]], ![![-1187431, -136346, 187304]], ![![-1355320, 341246, -159461]]]
  g := ![![![42174871278, -164139080201, -99834657050], ![443205791971, -1724898946445, -1049138904357], ![589998539746, -2296197112150, -1396620786043]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1683, -162, 242]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-1683, -162, 242]] 
 ![![31, 0, 0], ![16, 1, 0], ![19, 0, 1]] where
  M :=![![![-1683, -162, 242], ![38638, -1845, -1376], ![-37214, 5566, -1521]]]
  hmulB := by decide  
  f := ![![![-10465061, -1100570, -669402]], ![![-8948898, -941121, -572420]], ![![-11136627, -1171196, -712359]]]
  g := ![![![-119, -162, 242], ![3042, -1845, -1376], ![-3141, 5566, -1521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![915, -131, 33]] ![![-1560759866244, -164139080201, -99834657050]]
  ![![-10465061, -1100570, -669402]] where
 M := ![![![-10465061, -1100570, -669402]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-10465061, -1100570, -669402]] ![![-1683, -162, 242]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB238I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB238I0 : PrimesBelowBoundCertificateInterval O 1 31 238 where
  m := 11
  g := ![1, 3, 1, 3, 2, 3, 1, 2, 3, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB238I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N1]
    · exact ![I29N0, I29N1, I29N1]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![29, 29, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
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
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N1
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
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I3N0, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I13N0, I13N1, I19N1, I23N0, I23N1, I29N0, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0], [I3N0, I3N0, I3N0], [I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1], [I13N0, I13N1, I13N1], [], [I19N1], [I23N0, I23N0, I23N1], [I29N0, I29N1, I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
