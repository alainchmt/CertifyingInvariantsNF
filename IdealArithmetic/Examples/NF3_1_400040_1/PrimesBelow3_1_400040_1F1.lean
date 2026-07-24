
import IdealArithmetic.Examples.NF3_1_400040_1.RI3_1_400040_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [31, 16, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 20, 20], [13, 16, 17], [0, 1]]
 g := ![![[29, 0, 1], [1, 25], [19, 24, 33], [2, 1], []], ![[10, 2, 17, 24], [10, 28], [9, 29, 3, 29], [16, 34], [9, 30]], ![[28, 12, 29, 5], [26, 21], [35, 21, 36, 23], [14, 30], [12, 30]]]
 h' := ![![[26, 20, 20], [15, 1, 36], [3, 21, 5], [12, 11, 25], [0, 0, 1], [0, 1]], ![[13, 16, 17], [14, 17, 4], [18, 28, 19], [11, 36, 28], [27, 3, 16], [26, 20, 20]], ![[0, 1], [9, 19, 34], [1, 25, 13], [1, 27, 21], [19, 34, 20], [13, 16, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 29], []]
 b := ![[], [23, 24, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [31, 16, 35, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5295255, -306212, -169830]
  a := ![6, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143115, -8276, -4590]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1974568595991, -86682730681, -51222335315]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![1974568595991, -86682730681, -51222335315]] 
 ![![41, 0, 0], ![0, 41, 0], ![8, 11, 1]] where
  M :=![![![1974568595991, -86682730681, -51222335315], ![-5799949315076, 1805139650097, -969271977440], ![-12143487082430, -1099304012500, 1493869122739]]]
  hmulB := by decide  
  f := ![![![-39783361256297300689163, -4531745697084059060799, -4304453907920539856395]], ![![-498407486162128546524204, -56773885098815940910339, -53926364786681670320780]], ![![-158314881813492142919338, -18033739779317930144811, -17129249268654910983631]]]
  g := ![![![58154811671, 11628364824, -51222335315], ![47664061084, 304076375657, -969271977440], ![-587669269862, -427606447869, 1493869122739]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [38, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 40], [0, 1]]
 g := ![![[33, 39], [37], [18], [13, 2], [1]], ![[40, 2], [37], [18], [6, 39], [1]]]
 h' := ![![[17, 40], [31, 11], [17, 18], [39, 31], [3, 17], [0, 1]], ![[0, 1], [13, 30], [36, 23], [33, 10], [5, 24], [17, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [10, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [38, 24, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2531, 3208, 1790]
  a := ![-7, -3, 17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-411, -402, 1790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39783361256297300689163, -4531745697084059060799, -4304453907920539856395]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-39783361256297300689163, -4531745697084059060799, -4304453907920539856395]] 
 ![![41, 0, 0], ![11, 1, 0], ![5, 0, 1]] where
  M :=![![![-39783361256297300689163, -4531745697084059060799, -4304453907920539856395], ![-498407486162128546524204, -56773885098815940910339, -53926364786681670320780], ![-690160916519385442413310, -78616629288387313437130, -74673576097988657949131]]]
  hmulB := by decide  
  f := ![![![1974568595991, -86682730681, -51222335315]], ![![388300127825, 20771453966, -37383357705]], ![![-55381563475, -37383357705, 30189206004]]]
  g := ![![![770441730517806055161, -4531745697084059060799, -4304453907920539856395], ![9652123752640369636425, -56773885098815940910339, -53926364786681670320780], ![13365606979093129149775, -78616629288387313437130, -74673576097988657949131]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![1974568595991, -86682730681, -51222335315]] ![![-39783361256297300689163, -4531745697084059060799, -4304453907920539856395]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24052583, -1623915, -213749]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![24052583, -1623915, -213749]] 
 ![![43, 0, 0], ![0, 43, 0], ![15, 38, 1]] where
  M :=![![![24052583, -1623915, -213749], ![-19154220, 24607753, -16666648], ![-202137266, -10898312, 19522259]]]
  hmulB := by decide  
  f := ![![![-6947920873857, -791441686411, -751746564719]], ![![-87043821020636, -9915212011041, -9417909993548]], ![![-82149218545623, -9357665011375, -8888327020014]]]
  g := ![![![633926, 151129, -213749], ![5368500, 15300939, -16666648], ![-11510957, -17505678, 19522259]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [1, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 42], [0, 1]]
 g := ![![[34, 1], [34, 1], [4], [23, 38], [1]], ![[0, 42], [0, 42], [4], [21, 5], [1]]]
 h' := ![![[9, 42], [9, 42], [9, 42], [20, 41], [42, 9], [0, 1]], ![[0, 1], [0, 1], [0, 1], [2, 2], [37, 34], [9, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [42, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [1, 34, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1278823, 502712, 199374]
  a := ![66, 1, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39809, -164500, 199374]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6947920873857, -791441686411, -751746564719]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-6947920873857, -791441686411, -751746564719]] 
 ![![43, 0, 0], ![5, 1, 0], ![32, 0, 1]] where
  M :=![![![-6947920873857, -791441686411, -751746564719], ![-87043821020636, -9915212011041, -9417909993548], ![-120532385569766, -13729913773402, -13041283634993]]]
  hmulB := by decide  
  f := ![![![24052583, -1623915, -213749]], ![![2351365, 383446, -412451]], ![![13198730, -1461944, 294937]]]
  g := ![![![489887851842, -791441686411, -751746564719], ![6137333926235, -9915212011041, -9417909993548], ![8498564177140, -13729913773402, -13041283634993]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![24052583, -1623915, -213749]] ![![-6947920873857, -791441686411, -751746564719]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-347577321, -32184645, 43278113]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-347577321, -32184645, 43278113]] 
 ![![47, 0, 0], ![20, 1, 0], ![18, 0, 1]] where
  M :=![![![-347577321, -32184645, 43278113], ![5322112140, -99002111, -235290224], ![-2390701558, 401692244, -152277933]]]
  hmulB := by decide  
  f := ![![![109590094895539219, 12483471112116787, 11857356878507023]], ![![75845762529428936, 8639634689750921, 8206309839326008]], ![![82421029264743812, 9388627127644200, 8917736217105135]]]
  g := ![![![-10274265, -32184645, 43278113], ![245476136, -99002111, -235290224], ![-163479652, 401692244, -152277933]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22942790109, 12988691753, -8057425109]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-22942790109, 12988691753, -8057425109]] 
 ![![47, 0, 0], ![32, 1, 0], ![32, 0, 1]] where
  M :=![![![-22942790109, 12988691753, -8057425109], ![-1018845780092, -76218607407, 113772067312], ![1284690556654, -39803067652, -45309957257]]]
  hmulB := by decide  
  f := ![![![7981939135926667394023, 909227304867228875589, 863624591322960095573]], ![![7562129661466801118620, 861406564753735383301, 818202322418147489476]], ![![8380692873163860955934, 954649573772041481686, 906768685445395931425]]]
  g := ![![![-3845602611, 12988691753, -8057425109], ![-47245882916, -76218607407, 113772067312], ![85283135186, -39803067652, -45309957257]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80105498271938927157953442732881885313, -9124863652619893995916832926068745178, -8667201920450841511521898416908569628]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-80105498271938927157953442732881885313, -9124863652619893995916832926068745178, -8667201920450841511521898416908569628]] 
 ![![47, 0, 0], ![41, 1, 0], ![33, 0, 1]] where
  M :=![![![-80105498271938927157953442732881885313, -9124863652619893995916832926068745178, -8667201920450841511521898416908569628], ![-1003564775843621405398960478324753374648, -114316644221573240719646101891355988275, -108583040367100622982212126094504591036], ![-1389668503609715890901764497303140788712, -158297943228960409629368844050155131054, -150358437099883764218918499086470793437]]]
  hmulB := by decide  
  f := ![![![-96364566345265319231, 3784107520603768874, 2822064814002087292]], ![![-77179486650171121041, 1470426777636082387, 3387018344853775368]], ![![-55957182622238985145, 3840062305637667064, 452429286000502615]]]
  g := ![![![12341097337454350990528922446679137547, -9124863652619893995916832926068745178, -8667201920450841511521898416908569628], ![154609744028834085585521911922116886145, -114316644221573240719646101891355988275, -108583040367100622982212126094504591036], ![214093097724975002619716352736313952509, -158297943228960409629368844050155131054, -150358437099883764218918499086470793437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-347577321, -32184645, 43278113]] ![![-22942790109, 12988691753, -8057425109]]
  ![![96364566345265319231, -3784107520603768874, -2822064814002087292]] where
 M := ![![![96364566345265319231, -3784107520603768874, -2822064814002087292]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![96364566345265319231, -3784107520603768874, -2822064814002087292]] ![![-80105498271938927157953442732881885313, -9124863652619893995916832926068745178, -8667201920450841511521898416908569628]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [46, 28, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 40, 2], [51, 12, 51], [0, 1]]
 g := ![![[23, 16, 7], [47, 16], [3, 38, 15], [], [1]], ![[18, 44, 31, 33], [20, 29], [40, 4, 11, 26], [42, 9], [7, 19, 3, 8]], ![[32, 28, 45, 30], [41, 46], [30, 44, 51, 26], [51, 9], [48, 25, 38, 45]]]
 h' := ![![[2, 40, 2], [28, 10, 22], [21, 39, 4], [49, 32, 42], [7, 25], [0, 1]], ![[51, 12, 51], [25, 51, 19], [37, 27, 20], [45, 50, 38], [4, 46, 50], [2, 40, 2]], ![[0, 1], [18, 45, 12], [46, 40, 29], [33, 24, 26], [10, 35, 3], [51, 12, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 17], []]
 b := ![[], [35, 34, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [46, 28, 0, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15954749, -1220855, -367714]
  a := ![9, 3, -22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-301033, -23035, -6938]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2006104873526921, -228516566761084, -217055213281772]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-2006104873526921, -228516566761084, -217055213281772]] 
 ![![59, 0, 0], ![0, 59, 0], ![13, 28, 1]] where
  M :=![![![-2006104873526921, -228516566761084, -217055213281772], ![-25132559326768304, -2862864373174697, -2719276094174384], ![-34801865262910328, -3964300606468456, -3765469286739721]]]
  hmulB := by decide  
  f := ![![![63681213, 2407348, -5409308]], ![![-658746352, 34227325, 13254864]], ![![-296814861, 15786040, 5709411]]]
  g := ![![![13823947442985, 99136091612348, -217055213281772], ![173186947415232, 1241980784130645, -2719276094174384], ![239817550249255, 1719810837665148, -3765469286739721]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [40, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 58], [0, 1]]
 g := ![![[55, 26], [20, 41], [53], [57, 51], [42, 1]], ![[26, 33], [31, 18], [53], [16, 8], [25, 58]]]
 h' := ![![[42, 58], [26, 47], [32, 49], [21, 17], [31, 13], [0, 1]], ![[0, 1], [53, 12], [25, 10], [27, 42], [46, 46], [42, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [36, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [40, 17, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4224, 2803, 865]
  a := ![6, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-119, -363, 865]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63681213, -2407348, 5409308]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![-63681213, -2407348, 5409308]] 
 ![![59, 0, 0], ![13, 1, 0], ![43, 0, 1]] where
  M :=![![![-63681213, -2407348, 5409308], ![658746352, -34227325, -13254864], ![-104965288, 58284264, -36040061]]]
  hmulB := by decide  
  f := ![![![2006104873526921, 228516566761084, 217055213281772]], ![![867998689535903, 98874232899471, 93915150285380]], ![![2051938556348609, 233737508088052, 222014295895863]]]
  g := ![![![-4491287, -2407348, 5409308], ![28367131, -34227325, -13254864], ![11645117, 58284264, -36040061]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-2006104873526921, -228516566761084, -217055213281772]] ![![-63681213, -2407348, 5409308]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10362685815958692924924752515, -1180419536553648077392554176, -1121215051933187664100552482]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-10362685815958692924924752515, -1180419536553648077392554176, -1121215051933187664100552482]] 
 ![![61, 0, 0], ![0, 61, 0], ![16, 5, 1]] where
  M :=![![![-10362685815958692924924752515, -1180419536553648077392554176, -1121215051933187664100552482], ![-129824128085767927382496081136, -14788341539070983168034960749, -14046625469402856102126646724], ![-179771656152166149866525285508, -20477893357899680020269953146, -19450815200665115064313175759]]]
  hmulB := by decide  
  f := ![![![23667974936233, 14198625629692, -11618004891646]], ![![-1450955089516288, -48620675151689, 118750246513628]], ![![-91266638350076, -1573218051251, 6397054936845]]]
  g := ![![![124209098606103437716132577, 72551733165775249887052594, -1121215051933187664100552482], ![1556096384011110987730004368, 908930914884316349878660211, -14046625469402856102126646724], ![2154776837024191658401402076, 1258625945006981890185179109, -19450815200665115064313175759]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [31, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 60], [0, 1]]
 g := ![![[31, 57], [1], [24, 25], [3, 60], [15, 1]], ![[32, 4], [1], [33, 36], [49, 1], [30, 60]]]
 h' := ![![[15, 60], [52, 39], [49, 60], [29, 56], [23, 11], [0, 1]], ![[0, 1], [27, 22], [34, 1], [15, 5], [5, 50], [15, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [8, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [31, 46, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![370554, 150591, 65242]
  a := ![-43, -1, 108]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11038, -2879, 65242]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23667974936233, 14198625629692, -11618004891646]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![23667974936233, 14198625629692, -11618004891646]] 
 ![![61, 0, 0], ![9, 1, 0], ![29, 0, 1]] where
  M :=![![![23667974936233, 14198625629692, -11618004891646], ![-1450955089516288, -48620675151689, 118750246513628], ![1308822909247076, -80040935442938, -17642803154259]]]
  hmulB := by decide  
  f := ![![![-10362685815958692924924752515, -1180419536553648077392554176, -1121215051933187664100552482]], ![![-3657185252940920716505227111, -416592088000882227287999153, -395697720275435165230026542]], ![![-7873599095327348273595788663, -896886228163204496141869250, -851902486995533726610314717]]]
  g := ![![![3816434198799, 14198625629692, -11618004891646], ![-73067642000759, -48620675151689, 118750246513628], ![41652993765689, -80040935442938, -17642803154259]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-10362685815958692924924752515, -1180419536553648077392554176, -1121215051933187664100552482]] ![![23667974936233, 14198625629692, -11618004891646]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [6, 42, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 1, 24], [2, 65, 43], [0, 1]]
 g := ![![[64, 1, 16], [26, 1, 14], [28, 10], [5, 60], [20, 1], []], ![[42, 37, 37, 9], [63, 17, 58, 39], [56, 25], [7, 56], [47, 4], [44, 40]], ![[5, 0, 2, 34], [52, 34, 50, 2], [38, 21], [48, 6], [37, 1], [25, 40]]]
 h' := ![![[18, 1, 24], [45, 65, 63], [52, 49, 58], [32, 63, 55], [14, 25, 23], [0, 0, 1], [0, 1]], ![[2, 65, 43], [37, 32, 27], [59, 25, 55], [44, 31, 62], [35, 64, 18], [60, 25, 65], [18, 1, 24]], ![[0, 1], [22, 37, 44], [57, 60, 21], [34, 40, 17], [56, 45, 26], [55, 42, 1], [2, 65, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 55], []]
 b := ![[], [28, 47, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [6, 42, 47, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51590, 5628, 4556]
  a := ![-1, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![770, 84, 68]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [36, 23, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 55, 6], [6, 15, 65], [0, 1]]
 g := ![![[23, 42, 19], [19, 70, 6], [36, 4, 36], [58, 57], [30, 1], []], ![[31, 8, 64, 1], [16, 3, 46, 19], [45, 20, 39, 64], [43, 25], [7, 12], [36, 36]], ![[38, 28, 61, 66], [18, 27, 11, 56], [46, 15, 38, 26], [59, 45], [52, 43], [48, 36]]]
 h' := ![![[24, 55, 6], [26, 65, 44], [53, 27, 19], [54, 5, 6], [56, 55, 25], [0, 0, 1], [0, 1]], ![[6, 15, 65], [10, 9, 56], [14, 0, 21], [43, 34, 49], [61, 21, 66], [61, 19, 15], [24, 55, 6]], ![[0, 1], [21, 68, 42], [17, 44, 31], [14, 32, 16], [47, 66, 51], [12, 52, 55], [6, 15, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 23], []]
 b := ![[], [56, 41, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [36, 23, 41, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25218348, 2165074, 1010685]
  a := ![-10, -2, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![355188, 30494, 14235]
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


def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8868618054806703687, -63692772142365137, 557215543743221129]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-8868618054806703687, -63692772142365137, 557215543743221129]] 
 ![![73, 0, 0], ![15, 1, 0], ![37, 0, 1]] where
  M :=![![![-8868618054806703687, -63692772142365137, 557215543743221129], ![67120636337755996028, -6018847563948232905, 477503366062790888], ![11302195830185701946, 6925338207950048992, -5652710336632107187]]]
  hmulB := by decide  
  f := ![![![30715929533923749424335506887349203339, 3498869303690690215136256421163612349, 3323381904961126793965995860836578089]], ![![11582867046430530079183658642821547553, 1319411086443822553507850357367433790, 1253235416729398049983349230765177411]], ![![22867790328311505007008334036164351513, 2604883226294570374757270080544482655, 2474234110337446328700627969118483368]]]
  g := ![![![-390824679331101485, -63692772142365137, 557215543743221129], ![1914188017159674339, -6018847563948232905, 477503366062790888], ![1596882262552368945, 6925338207950048992, -5652710336632107187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![96599, -3958, -2710]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![96599, -3958, -2710]] 
 ![![73, 0, 0], ![42, 1, 0], ![61, 0, 1]] where
  M :=![![![96599, -3958, -2710], ![-309368, 87007, -45000], ![-567100, -55020, 72423]]]
  hmulB := by decide  
  f := ![![![-3825407961, -435754434, -413898970]], ![![-2857424562, -325490885, -309165740]], ![![-4105657297, -467677798, -444221203]]]
  g := ![![![5865, -3958, -2710], ![-16694, 87007, -45000], ![-36631, -55020, 72423]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-8868618054806703687, -63692772142365137, 557215543743221129]] ![![-8868618054806703687, -63692772142365137, 557215543743221129]]
  ![![80675046000741486893534037129485335167, 4807130050581244330198904184785945072, -8121923408601301343935673445564228402]] where
 M := ![![![80675046000741486893534037129485335167, 4807130050581244330198904184785945072, -8121923408601301343935673445564228402]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI73N1 : IdealMulLeCertificate' Table 
  ![![80675046000741486893534037129485335167, 4807130050581244330198904184785945072, -8121923408601301343935673445564228402]] ![![96599, -3958, -2710]]
  ![![73, 0, 0]] where
 M := ![![![10911899324155206488629440273811769563536737, 545810358181231120256349090422111612966558, -1023164285959297471572281206884370900100616]]]
 hmul := by decide  
 g := ![![![![149478072933632965597663565394681774842969, 7476854221660700277484234115371391958446, -14015949122730102350305222012114669864392]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46525635, 5299762, 5033950]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![46525635, 5299762, 5033950]] 
 ![![79, 0, 0], ![7, 1, 0], ![27, 0, 1]] where
  M :=![![![46525635, 5299762, 5033950], ![582874952, 66395623, 63065520], ![807125740, 91940160, 87328859]]]
  hmulB := by decide  
  f := ![![![-99043, 442, 5390]], ![![-611, -879, 670]], ![![-30859, 1066, 1009]]]
  g := ![![![-1601131, 5299762, 5033950], ![-20059031, 66395623, 63065520], ![-27776387, 91940160, 87328859]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-231537071415, -26374521759, -25051695493]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-231537071415, -26374521759, -25051695493]] 
 ![![79, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![-231537071415, -26374521759, -25051695493], ![-2900705372124, -330421027121, -313848608576], ![-4016700257842, -457544650204, -434596287891]]]
  hmulB := by decide  
  f := ![![![-342307, -610303, 460469]], ![![669686, -75619, 16006]], ![![-785195, -63283, 90962]]]
  g := ![![![5865547780, -26374521759, -25051695493], ![73483809102, -330421027121, -313848608576], ![101755399843, -457544650204, -434596287891]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3176620605, 979743389, -524420879]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![-3176620605, 979743389, -524420879]] 
 ![![79, 0, 0], ![57, 1, 0], ![28, 0, 1]] where
  M :=![![![-3176620605, 979743389, -524420879], ![-66849479036, -6778468389, 8748592132], ![99738896794, -1918754482, -4363659101]]]
  hmulB := by decide  
  f := ![![![-46365325640965593913, -5281501068090062967, -5016604953551321417]], ![![-40806204451757432547, -4648258357237540850, -4415122822030741687]], ![![-26614858411880874858, -3031713919533408308, -2879656913897349975]]]
  g := ![![![-561243154, 979743389, -524420879], ![943830879, -6778468389, 8748592132], ![4193548824, -1918754482, -4363659101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![46525635, 5299762, 5033950]] ![![-231537071415, -26374521759, -25051695493]]
  ![![-46365325640965593913, -5281501068090062967, -5016604953551321417]] where
 M := ![![![-46365325640965593913, -5281501068090062967, -5016604953551321417]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![-46365325640965593913, -5281501068090062967, -5016604953551321417]] ![![-3176620605, 979743389, -524420879]]
  ![![79, 0, 0]] where
 M := ![![![79, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB179I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB179I1 : PrimesBelowBoundCertificateInterval O 31 79 179 where
  m := 11
  g := ![1, 2, 2, 3, 1, 2, 2, 1, 1, 3, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB179I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
    · exact ![I73N0, I73N0, I73N1]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I43N1, I47N0, I47N1, I47N2, I59N1, I61N1, I73N0, I73N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [I43N1], [I47N0, I47N1, I47N2], [], [I59N1], [I61N1], [], [], [I73N0, I73N0, I73N1], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
