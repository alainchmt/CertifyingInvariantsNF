
import IdealArithmetic.Examples.NF3_1_195615_2.RI3_1_195615_2
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
  c := ![-215022, -22472, -10490]
  a := ![2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-107511, -11236, -5245]
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


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![432159, 142903, -87816]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![432159, 142903, -87816]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![432159, 142903, -87816], ![-7750166, -292727, 538883], ![6350899, -953989, 103253]]]
  hmulB := by decide  
  f := ![![![-483863513356, -69020334565, -51301883117]], ![![-1407539798605, -200777419937, -149235146353]], ![![-3406793250153, -485959373726, -361207043513]]]
  g := ![![![202597, 142903, -87816], ![-2942644, -292727, 538883], ![2048131, -953989, 103253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![432159, 142903, -87816]] ![![432159, 142903, -87816]]
  ![![-1478471117201, 103700749120, 29990257157]] where
 M := ![![![-1478471117201, 103700749120, 29990257157]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-1478471117201, 103700749120, 29990257157]] ![![432159, 142903, -87816]]
  ![![3, 0, 0]] where
 M := ![![![-1252167525354686736, -270244342683974016, 188812574438387697]]]
 hmul := by decide  
 g := ![![![![-417389175118228912, -90081447561324672, 62937524812795899]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4697, -670, -498]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-4697, -670, -498]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![-4697, -670, -498], ![-40990, -5847, -4346], ![-89818, -12812, -9523]]]
  hmulB := by decide  
  f := ![![![-29, 34, -14]], ![![-269, -13, 20]], ![![370, 8, -23]]]
  g := ![![![-139, -670, -498], ![-1213, -5847, -4346], ![-2658, -12812, -9523]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13891, -1064, 1212]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-13891, -1064, 1212]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![-13891, -1064, 1212], ![105148, -5703, -2896], ![-10448, 17708, -7535]]]
  hmulB := by decide  
  f := ![![![94254473, 13444856, 9993380]], ![![239913096, 34222217, 25436912]], ![![360475168, 51419700, 38219569]]]
  g := ![![![-1927, -1064, 1212], ![25592, -5703, -2896], ![-16256, 17708, -7535]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-4697, -670, -498]] ![![-4697, -670, -498]]
  ![![94254473, 13444856, 9993380]] where
 M := ![![![94254473, 13444856, 9993380]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![94254473, 13444856, 9993380]] ![![-13891, -1064, 1212]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-529575029, -572841704, 289120818]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-529575029, -572841704, 289120818]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![-529575029, -572841704, 289120818], ![25720952938, 2061712469, -2285966884], ![-29609570852, 2629087022, 348587289]]]
  hmulB := by decide  
  f := ![![![6728692627712385989, 959809127017324452, 713413169600050694]], ![![12233610238974172006, 1745053818535326909, 1297074950383846632]], ![![23187501161233979167, 3307563070367743958, 2458466988135377603]]]
  g := ![![![45169671, -572841704, 289120818], ![4129133926, 2061712469, -2285966884], ![-5981265055, 2629087022, 348587289]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -4, -3]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-28, -4, -3]] 
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![-28, -4, -3], ![-247, -35, -26], ![-538, -77, -57]]]
  hmulB := by decide  
  f := ![![![7, -3, 1]], ![![19, 0, -1]], ![![-21, -2, 2]]]
  g := ![![![2, -4, -3], ![17, -35, -26], ![38, -77, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-529575029, -572841704, 289120818]] ![![-529575029, -572841704, 289120818]]
  ![![-23014328143526572447, -117548431497973764, 1257169841681359016]] where
 M := ![![![-23014328143526572447, -117548431497973764, 1257169841681359016]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-23014328143526572447, -117548431497973764, 1257169841681359016]] ![![-28, -4, -3]]
  ![![7, 0, 0]] where
 M := ![![![-2921724225827602384, -630570132929272704, 440562673689571293]]]
 hmul := by decide  
 g := ![![![![-417389175118228912, -90081447561324672, 62937524812795899]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5119947, -2972382, 1624247]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-5119947, -2972382, 1624247]] 
 ![![11, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![-5119947, -2972382, 1624247], ![144005759, 8946052, -11613416], ![-145452168, 15998783, 305018]]]
  hmulB := by decide  
  f := ![![![188529229361664, 26892605304277, 19988910554068]], ![![149570198771566, 21335324683950, 15858258875411]], ![![396296042261699, 56529340751435, 42017496005906]]]
  g := ![![![-1056085, -2972382, 1624247], ![17314493, 8946052, -11613416], ![-13333840, 15998783, 305018]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![40477, 349, -2276]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![40477, 349, -2276]] 
 ![![11, 0, 0], ![4, 1, 0], ![9, 0, 1]] where
  M :=![![![40477, 349, -2276], ![-194158, 28399, -2807], ![-120551, -41499, 25243]]]
  hmulB := by decide  
  f := ![![![600388264, 85641917, 63656481]], ![![694642737, 99086773, 73649861]], ![![1534944097, 218950907, 162743254]]]
  g := ![![![5415, 349, -2276], ![-25681, 28399, -2807], ![-16522, -41499, 25243]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3259825, -696764, 147510]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![3259825, -696764, 147510]] 
 ![![11, 0, 0], ![7, 1, 0], ![8, 0, 1]] where
  M :=![![![3259825, -696764, 147510], ![13931878, 5390903, -3188800], ![-49489280, -681130, 2898867]]]
  hmulB := by decide  
  f := ![![![-13455523462901, -1919352680088, -1426628941670]], ![![-19237583538371, -2744130142881, -2039674897770]], ![![-33176970514628, -4732503157534, -3517605722557]]]
  g := ![![![632463, -696764, 147510], ![155087, 5390903, -3188800], ![-6173846, -681130, 2898867]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-5119947, -2972382, 1624247]] ![![40477, 349, -2276]]
  ![![174067049540, -153604164174, 60997342667]] where
 M := ![![![174067049540, -153604164174, 60997342667]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![174067049540, -153604164174, 60997342667]] ![![3259825, -696764, 147510]]
  ![![11, 0, 0]] where
 M := ![![![-4591280926300518032, -990895923174571392, 692312772940754889]]]
 hmul := by decide  
 g := ![![![![-417389175118228912, -90081447561324672, 62937524812795899]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![135322, 2111, -8040]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![135322, 2111, -8040]] 
 ![![13, 0, 0], ![0, 1, 0], ![10, 0, 1]] where
  M :=![![![135322, 2111, -8040], ![-687622, 90900, -5525], ![-351205, -142205, 83264]]]
  hmulB := by decide  
  f := ![![![6783014975, 967557896, 719172725]], ![![4553428141, 649520216, 482779610]], ![![15195228520, 2167511555, 1611082084]]]
  g := ![![![16594, 2111, -8040], ![-48644, 90900, -5525], ![-91065, -142205, 83264]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1311, -187, -139]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-1311, -187, -139]] 
 ![![13, 0, 0], ![1, 1, 0], ![5, 0, 1]] where
  M :=![![![-1311, -187, -139], ![-11441, -1632, -1213], ![-25069, -3576, -2658]]]
  hmulB := by decide  
  f := ![![![-168, -18, 17]], ![![101, -5, -3]], ![![-96, 11, 0]]]
  g := ![![![-33, -187, -139], ![-288, -1632, -1213], ![-631, -3576, -2658]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1211048, -172749, -128402]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![-1211048, -172749, -128402]] 
 ![![13, 0, 0], ![12, 1, 0], ![12, 0, 1]] where
  M :=![![![-1211048, -172749, -128402], ![-10568672, -1507560, -1120549], ![-23158197, -3303383, -2455360]]]
  hmulB := by decide  
  f := ![![![-4333, 674, -81]], ![![-4633, 154, 172]], ![![-4, 763, -348]]]
  g := ![![![184828, -172749, -128402], ![1612972, -1507560, -1120549], ![3534363, -3303383, -2455360]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![135322, 2111, -8040]] ![![-1311, -187, -139]]
  ![![-4333, 674, -81]] where
 M := ![![![-4333, 674, -81]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-4333, 674, -81]] ![![-1211048, -172749, -128402]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [5, 0, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 8, 4], [8, 8, 13], [0, 1]]
 g := ![![[3, 15, 13], [9, 4], [10, 1], []], ![[9, 3, 12, 2], [3, 4], [8, 13], [3, 16]], ![[5, 14, 3, 2], [7, 16], [14, 13], [11, 16]]]
 h' := ![![[2, 8, 4], [7, 4, 9], [1, 12, 15], [0, 0, 1], [0, 1]], ![[8, 8, 13], [1, 8, 3], [13, 5, 15], [6, 3, 8], [2, 8, 4]], ![[0, 1], [1, 5, 5], [11, 0, 4], [9, 14, 8], [8, 8, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 1], []]
 b := ![[], [6, 2, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [5, 0, 7, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2078828, 329732, -21352]
  a := ![-5, -7, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![122284, 19396, -1256]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44050741463, -6283583758, -4670502998]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-44050741463, -6283583758, -4670502998]] 
 ![![19, 0, 0], ![10, 1, 0], ![14, 0, 1]] where
  M :=![![![-44050741463, -6283583758, -4670502998], ![-384425587314, -54836088937, -40758924786], ![-842357817298, -120157475752, -89311429965]]]
  hmulB := by decide  
  f := ![![![-8133, 203974, -92662]], ![![-440292, 61071, -4846]], ![![584644, 111312, -81373]]]
  g := ![![![4430112531, -6283583758, -4670502998], ![38661065740, -54836088937, -40758924786], ![84714576828, -120157475752, -89311429965]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 6, -3]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![5, 6, -3]] 
 ![![19, 0, 0], ![11, 1, 0], ![14, 0, 1]] where
  M :=![![![5, 6, -3], ![-267, -22, 24], ![312, -27, -4]]]
  hmulB := by decide  
  f := ![![![-736, -105, -78]], ![![-764, -109, -81]], ![![-1283, -183, -136]]]
  g := ![![![-1, 6, -3], ![-19, -22, 24], ![35, -27, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26586, -715, -1064]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![26586, -715, -1064]] 
 ![![19, 0, 0], ![17, 1, 0], ![17, 0, 1]] where
  M :=![![![26586, -715, -1064], ![-89010, 22696, -5703], ![-130999, -23791, 17708]]]
  hmulB := by decide  
  f := ![![![266220695, 37974844, 28226189]], ![![360475168, 51419700, 38219569]], ![![506133791, 72197061, 53663101]]]
  g := ![![![2991, -715, -1064], ![-19889, 22696, -5703], ![-1452, -23791, 17708]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-44050741463, -6283583758, -4670502998]] ![![5, 6, -3]]
  ![![266220695, 37974844, 28226189]] where
 M := ![![![266220695, 37974844, 28226189]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![266220695, 37974844, 28226189]] ![![26586, -715, -1064]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19384331088921754341808954058656402308586851074, -2765062833104648413391383104282856555477182529, -2055233883885412775842745977708401198682854894]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-19384331088921754341808954058656402308586851074, -2765062833104648413391383104282856555477182529, -2055233883885412775842745977708401198682854894]] 
 ![![23, 0, 0], ![6, 1, 0], ![4, 0, 1]] where
  M :=![![![-19384331088921754341808954058656402308586851074, -2765062833104648413391383104282856555477182529, -2055233883885412775842745977708401198682854894], ![-169164754464050789119850641896648388777088300932, -24130374842139521394239917738632695191046760486, -17935781933294067618642407476831085174751622433], ![-370675777150332358343888798392797286328628937969, -52874757959346084807969089097873905552360155631, -39301093942328940599490942111180923810321200390]]]
  hmulB := by decide  
  f := ![![![639924333948225291080683, -122718644308306814021804, 22540356523154278845427]], ![![260909286816264307669087, 11380501710033453444374, -18837842145926079971548]], ![![-277553213038478070597062, -29400044558036088179701, 27931781177665596971164]]]
  g := ![![![235955715010773358343927325124971383435115812, -2765062833104648413391383104282856555477182529, -2055233883885412775842745977708401198682854894], ![2059157492259243900876456280107483611660815292, -24130374842139521394239917738632695191046760486, -17935781933294067618642407476831085174751622433], ![4512049842393909256603891506050862705513773799, -52874757959346084807969089097873905552360155631, -39301093942328940599490942111180923810321200390]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![908, 34, -63]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![908, 34, -63]] 
 ![![23, 0, 0], ![20, 1, 0], ![15, 0, 1]] where
  M :=![![![908, 34, -63], ![-5423, 525, 44], ![-1268, -1027, 535]]]
  hmulB := by decide  
  f := ![![![326063, 46511, 34571]], ![![407251, 58092, 43179]], ![![483742, 69003, 51289]]]
  g := ![![![51, 34, -63], ![-721, 525, 44], ![489, -1027, 535]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-19384331088921754341808954058656402308586851074, -2765062833104648413391383104282856555477182529, -2055233883885412775842745977708401198682854894]] ![![908, 34, -63]]
  ![![-320047741196772457810999829475914239914833, -45652961143861480448636289339070181788103, -33933229841731125848967086984295351781904]] where
 M := ![![![-320047741196772457810999829475914239914833, -45652961143861480448636289339070181788103, -33933229841731125848967086984295351781904]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-320047741196772457810999829475914239914833, -45652961143861480448636289339070181788103, -33933229841731125848967086984295351781904]] ![![908, 34, -63]]
  ![![23, 0, 0]] where
 M := ![![![-5284193515642942981782266027946331523, -753759674554218847772321603315842989, -560259392626844399010534504087360693]]]
 hmul := by decide  
 g := ![![![![-229747544158388825294881131649840501, -32772159763226906424883547970254043, -24359104027254104304805848003798291]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163412395, 23309834, 17325885]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![163412395, 23309834, 17325885]] 
 ![![29, 0, 0], ![0, 29, 0], ![7, 27, 1]] where
  M :=![![![163412395, 23309834, 17325885], ![1426080557, 203422152, 151200940], ![3124844300, 445740985, 331313258]]]
  hmulB := by decide  
  f := ![![![-1196, -2843, 1360]], ![![121286, 11290, -11495]], ![![107395, 10226, -10283]]]
  g := ![![![1452800, -15327209, 17325885], ![12678413, -133758732, 151200940], ![27781086, -293093689, 331313258]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [16, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 28], [0, 1]]
 g := ![![[1, 20], [13], [27, 6], [13, 1]], ![[0, 9], [13], [18, 23], [26, 28]]]
 h' := ![![[13, 28], [4, 22], [3, 19], [24, 8], [0, 1]], ![[0, 1], [0, 7], [18, 10], [12, 21], [13, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [12, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [16, 16, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![314014, 606319, 212156]
  a := ![66, 67, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40382, -176617, 212156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1196, -2843, 1360]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-1196, -2843, 1360]] 
 ![![29, 0, 0], ![8, 1, 0], ![19, 0, 1]] where
  M :=![![![-1196, -2843, 1360], ![121286, 11290, -11495], ![-151895, 11625, 2638]]]
  hmulB := by decide  
  f := ![![![163412395, 23309834, 17325885]], ![![94254473, 13444856, 9993380]], ![![214816545, 30642339, 22776037]]]
  g := ![![![-148, -2843, 1360], ![8599, 11290, -11495], ![-10173, 11625, 2638]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![163412395, 23309834, 17325885]] ![![-1196, -2843, 1360]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4178, 596, 443]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![4178, 596, 443]] 
 ![![31, 0, 0], ![0, 31, 0], ![13, 18, 1]] where
  M :=![![![4178, 596, 443], ![36463, 5201, 3866], ![79898, 11397, 8471]]]
  hmulB := by decide  
  f := ![![![-101, 5, 3]], ![![245, -96, 31]], ![![120, -51, 17]]]
  g := ![![![-51, -238, 443], ![-445, -2077, 3866], ![-975, -4551, 8471]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [5, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 30], [0, 1]]
 g := ![![[9, 25], [14, 1], [9, 25], [17, 1]], ![[0, 6], [0, 30], [0, 6], [3, 30]]]
 h' := ![![[17, 30], [23, 26], [17, 30], [8, 5], [0, 1]], ![[0, 1], [0, 5], [0, 1], [0, 26], [17, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [20, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [5, 14, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2708, 2088, 612]
  a := ![5, 6, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-344, -288, 612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, -5, -3]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![101, -5, -3]] 
 ![![31, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![101, -5, -3], ![-245, 96, -31], ![-623, -82, 70]]]
  hmulB := by decide  
  f := ![![![-4178, -596, -443]], ![![-1311, -187, -139]], ![![-3386, -483, -359]]]
  g := ![![![4, -5, -3], ![-5, 96, -31], ![-31, -82, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![4178, 596, 443]] ![![101, -5, -3]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB126I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB126I0 : PrimesBelowBoundCertificateInterval O 1 31 126 where
  m := 11
  g := ![1, 3, 3, 3, 3, 3, 1, 3, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB126I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N1]
    · exact ![I29N0, I29N1]
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
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
    · exact ![841, 29]
    · exact ![961, 31]
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
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
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
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I11N2, I13N0, I13N1, I13N2, I19N0, I19N1, I19N2, I23N0, I23N1, I29N1, I31N1]
  Il := ![[I2N0], [I3N0, I3N0, I3N0], [I5N0, I5N0, I5N1], [I7N0, I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N0, I13N1, I13N2], [], [I19N0, I19N1, I19N2], [I23N0, I23N1, I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
