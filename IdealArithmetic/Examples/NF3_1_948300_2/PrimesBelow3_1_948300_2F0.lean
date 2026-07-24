
import IdealArithmetic.Examples.NF3_1_948300_2.RI3_1_948300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-1, 1, 3], ![197, 20, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 0, -1], ![-1, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-2, 1, 3], ![99, 20, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![-13, -1, 1]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![-1, 1, 3]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![6, 1, 1], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-13, -1, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![-26, -2, 2], ![198, 6, -4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![-13, -1, 1]], ![![99, 3, -2]]]]
 hle2 := by decide  

def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1324846, 287574, 73583]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![1324846, 287574, 73583]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![1324846, 287574, 73583], ![14208277, 3084080, 789139], ![46497624, 10092877, 2582515]]]
  hmulB := by decide  
  f := ![![![-1703, -319, 146]], ![![9126, 193, -319]], ![![-28799, 532, 658]]]
  g := ![![![296702, 287574, 73583], ![3181973, 3084080, 789139], ![10413239, 10092877, 2582515]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![100853596567585, 21891504509055, 5601488928076]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![100853596567585, 21891504509055, 5601488928076]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![100853596567585, 21891504509055, 5601488928076], ![1081601814321917, 234774879638160, 60073024599089], ![3539620916209347, 768317936937584, 196593359548126]]]
  hmulB := by decide  
  f := ![![![-30172816, 1927454, 270735]], ![![7078175, -6967736, 1927454]], ![![104058064, 18816633, -8714700]]]
  g := ![![![24453534376818, 21891504509055, 5601488928076], ![262251303361556, 234774879638160, 60073024599089], ![858236539907879, 768317936937584, 196593359548126]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![1324846, 287574, 73583]] ![![100853596567585, 21891504509055, 5601488928076]]
  ![![705111970027422056569, 153053162173545947842, 39162479352093951840]] where
 M := ![![![705111970027422056569, 153053162173545947842, 39162479352093951840]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![705111970027422056569, 153053162173545947842, 39162479352093951840]] ![![100853596567585, 21891504509055, 5601488928076]]
  ![![3, 0, 0]] where
 M := ![![![375275987100023033223274894357017459, 81458234939939553238239625957537575, 20843126653444511612334689805299022]]]
 hmul := by decide  
 g := ![![![![125091995700007677741091631452339153, 27152744979979851079413208652512525, 6947708884481503870778229935099674]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-705061, 111893, -14102]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-705061, 111893, -14102]] 
 ![![5, 0, 0], ![0, 1, 0], ![3, 0, 1]] where
  M :=![![![-705061, 111893, -14102], ![-2889987, -875208, 349781], ![23988997, 1405842, -1113096]]]
  hmulB := by decide  
  f := ![![![-482453703366, -104722466844, -26795862217]], ![![-1034812477981, -224618682910, -57474307663]], ![![-3675971618484, -797914521643, -204166385946]]]
  g := ![![![-132551, 111893, -14102], ![-787866, -875208, 349781], ![5465657, 1405842, -1113096]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-705061, 111893, -14102]] ![![-705061, 111893, -14102]]
  ![![-164551137364, -196646223101, 64777695447]] where
 M := ![![![-164551137364, -196646223101, 64777695447]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-164551137364, -196646223101, 64777695447]] ![![-705061, 111893, -14102]]
  ![![5, 0, 0]] where
 M := ![![![2238275559566985550, 244761432137311330, -138566406114657665]]]
 hmul := by decide  
 g := ![![![![447655111913397110, 48952286427462266, -27713281222931533]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [5, 6, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6, 2], [4, 0, 5], [0, 1]]
 g := ![![[1, 4, 1], [1]], ![[5, 5, 5, 1], [4, 2, 1, 1]], ![[6, 4, 0, 5], [2, 4, 1, 6]]]
 h' := ![![[2, 6, 2], [2, 1, 6], [0, 1]], ![[4, 0, 5], [2, 3, 2], [2, 6, 2]], ![[0, 1], [5, 3, 6], [4, 0, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [5, 6, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448210, -88221, -16485]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64030, -12603, -2355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-9, -3, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-9, -3, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![2, 8, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-9, -3, 1], ![200, 8, -10], ![-729, -1, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -8, 11]], ![![-1, -1, 1], ![20, 8, -10], ![-69, -11, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 7, 1] where
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
 g := ![![[2, 5], [3, 5], [1]], ![[0, 6], [1, 6], [1]]]
 h' := ![![[4, 10], [6, 4], [2, 4], [0, 1]], ![[0, 1], [0, 7], [7, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [2, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8835, 3776, 1352]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1049, -640, 1352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-1, 1, 0]] 
 ![![11, 0, 0], ![10, 1, 0], ![7, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-1, 1, 0], ![-1, 0, 3], ![197, 20, -2]]]
  hmulB := by decide  
  f := ![![![-98, -1, 300], ![11, -1100, 0]], ![![-88, -1, 270], ![12, -990, 0]], ![![-62, -1, 191], ![11, -700, 0]]]
  g := ![![![1, 0, 0], ![-10, 11, 0], ![-7, 0, 11]], ![![-1, 1, 0], ![-2, 0, 3], ![1, 20, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-9, -3, 1]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-11, 11, 0]], ![![-99, -33, 11], ![209, 11, -11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-1, 1, 0]]], ![![![-9, -3, 1]], ![![19, 1, -1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-19, 1, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-19, 1, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![7, 1, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-19, 1, 1], ![196, 2, 2], ![59, 79, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -1, 13]], ![![-2, 0, 1], ![14, 0, 2], ![4, 6, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [8, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 12], [0, 1]]
 g := ![![[10, 3], [3], [11, 1]], ![[4, 10], [3], [9, 12]]]
 h' := ![![[11, 12], [11, 9], [3, 9], [0, 1]], ![[0, 1], [6, 4], [11, 4], [11, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [1, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [8, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1065905, 440211, 97713]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29378, 26346, 97713]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-2, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-2, 1, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-2, 1, 0], ![-1, -1, 3], ![197, 20, -3]]]
  hmulB := by decide  
  f := ![![![-45, -49, 144], ![13, -624, 0]], ![![-37, -41, 120], ![14, -520, 0]], ![![-42, -45, 133], ![9, -576, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-12, 0, 13]], ![![-1, 1, 0], ![-2, -1, 3], ![1, 20, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-19, 1, 1]] ![![13, 0, 0], ![-2, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-26, 13, 0]], ![![-247, 13, 13], ![234, 0, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-2, 1, 0]]], ![![![-19, 1, 1]], ![![18, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4112296811, 892624232, 228400234]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![4112296811, 892624232, 228400234]] 
 ![![17, 0, 0], ![0, 17, 0], ![5, 2, 1]] where
  M :=![![![4112296811, 892624232, 228400234], ![44102221866, 9572925723, 2449472462], ![144327741412, 31328098446, 8016077493]]]
  hmulB := by decide  
  f := ![![![-55389, -10236, 4706]], ![![937318, 28495, -35414]], ![![-62837, 4632, 375]]]
  g := ![![![174723273, 25636692, 228400234], ![1873815268, 274940047, 2449472462], ![6132197291, 899761380, 8016077493]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 16], [0, 1]]
 g := ![![[15, 4], [9], [2], [1]], ![[8, 13], [9], [2], [1]]]
 h' := ![![[11, 16], [14, 2], [15, 3], [3, 11], [0, 1]], ![[0, 1], [2, 15], [14, 14], [5, 6], [11, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [2, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 6, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5640, 4085, 1235]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-695, 95, 1235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55389, 10236, -4706]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![55389, 10236, -4706]] 
 ![![17, 0, 0], ![12, 1, 0], ![10, 0, 1]] where
  M :=![![![55389, 10236, -4706], ![-937318, -28495, 35414], ![2665920, -72934, -53673]]]
  hmulB := by decide  
  f := ![![![-4112296811, -892624232, -228400234]], ![![-5497046094, -1193200971, -305310310]], ![![-10908865266, -2367902398, -605887049]]]
  g := ![![![-1199, 10236, -4706], ![-55854, -28495, 35414], ![239874, -72934, -53673]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![4112296811, 892624232, 228400234]] ![![55389, 10236, -4706]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![3, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![3, 1, 0]] 
 ![![19, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![3, 1, 0], ![-1, 4, 3], ![197, 20, 2]]]
  hmulB := by decide  
  f := ![![![-119, 467, 351], ![19, -2223, 0]], ![![-18, 72, 54], ![1, -342, 0]], ![![-13, 49, 37], ![5, -234, 0]]]
  g := ![![![1, 0, 0], ![-3, 19, 0], ![-2, 0, 19]], ![![0, 1, 0], ![-1, 4, 3], ![7, 20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85226922, -18499544, -4733571]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-85226922, -18499544, -4733571]] 
 ![![19, 0, 0], ![7, 1, 0], ![0, 0, 1]] where
  M :=![![![-85226922, -18499544, -4733571], ![-914013943, -198397886, -50765061], ![-2991177370, -649271569, -166132369]]]
  hmulB := by decide  
  f := ![![![78775, -3163, -1278]], ![![15938, 1469, -903]], ![![-23513, -7298, 2900]]]
  g := ![![![2329994, -18499544, -4733571], ![24987961, -198397886, -50765061], ![81774927, -649271569, -166132369]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![9, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![9, 1, 0]] 
 ![![19, 0, 0], ![9, 1, 0], ![14, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![9, 1, 0], ![-1, 10, 3], ![197, 20, 8]]]
  hmulB := by decide  
  f := ![![![120, -1190, -357], ![0, 2261, 0]], ![![56, -560, -168], ![1, 1064, 0]], ![![87, -877, -263], ![3, 1666, 0]]]
  g := ![![![1, 0, 0], ![-9, 19, 0], ![-14, 0, 19]], ![![0, 1, 0], ![-7, 10, 3], ![-5, 20, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![3, 1, 0]] ![![-85226922, -18499544, -4733571]]
  ![![19, 0, 0], ![-6, -9, 1]] where
 M := ![![![-1619311518, -351491336, -89937849]], ![![-1169694709, -253896518, -64965774]]]
 hmul := by decide  
 g := ![![![![-76795302, -5852114, -6138841], ![26700130, 0, 0]]], ![![![-55472377, -4227221, -4434335], ![19286591, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-6, -9, 1]] ![![19, 0, 0], ![9, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![171, 19, 0]], ![![-114, -171, 19], ![152, -76, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![9, 1, 0]]], ![![![-6, -9, 1]], ![![8, -4, -1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![3, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![3, 1, 0]] 
 ![![23, 0, 0], ![3, 1, 0], ![11, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![3, 1, 0], ![-1, 4, 3], ![197, 20, 2]]]
  hmulB := by decide  
  f := ![![![-18, 63, 48], ![23, -368, 0]], ![![-2, 8, 6], ![1, -46, 0]], ![![-9, 30, 23], ![14, -176, 0]]]
  g := ![![![1, 0, 0], ![-3, 23, 0], ![-11, 0, 23]], ![![0, 1, 0], ![-2, 4, 3], ![5, 20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![4, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![4, 1, 0]] 
 ![![23, 0, 0], ![4, 1, 0], ![16, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![4, 1, 0], ![-1, 5, 3], ![197, 20, 3]]]
  hmulB := by decide  
  f := ![![![-129, 629, 378], ![23, -2898, 0]], ![![-21, 105, 63], ![1, -483, 0]], ![![-88, 438, 263], ![6, -2016, 0]]]
  g := ![![![1, 0, 0], ![-4, 23, 0], ![-16, 0, 23]], ![![0, 1, 0], ![-3, 5, 3], ![3, 20, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-7, 1, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-7, 1, 0]] 
 ![![23, 0, 0], ![16, 1, 0], ![1, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-7, 1, 0], ![-1, -6, 3], ![197, 20, -8]]]
  hmulB := by decide  
  f := ![![![-122, -781, 390], ![23, -2990, 0]], ![![-82, -541, 270], ![24, -2070, 0]], ![![-5, -34, 17], ![2, -130, 0]]]
  g := ![![![1, 0, 0], ![-16, 23, 0], ![-1, 0, 23]], ![![-1, 1, 0], ![4, -6, 3], ![-5, 20, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![3, 1, 0]] ![![23, 0, 0], ![4, 1, 0]]
  ![![23, 0, 0], ![-4, -5, 1]] where
 M := ![![![529, 0, 0], ![92, 23, 0]], ![![69, 23, 0], ![11, 8, 3]]]
 hmul := by decide  
 g := ![![![![23, 0, 0], ![0, 0, 0]], ![![4, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-4, -5, 1]] ![![23, 0, 0], ![-7, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-161, 23, 0]], ![![-92, -115, 23], ![230, 46, -23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-7, 1, 0]]], ![![![-4, -5, 1]], ![![10, 2, -1]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![14, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![14, 1, 0]] 
 ![![29, 0, 0], ![14, 1, 0], ![7, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![14, 1, 0], ![-1, 15, 3], ![197, 20, 13]]]
  hmulB := by decide  
  f := ![![![541, -8100, -1620], ![0, 15660, 0]], ![![260, -3900, -780], ![1, 7540, 0]], ![![119, -1956, -391], ![24, 3780, 0]]]
  g := ![![![1, 0, 0], ![-14, 29, 0], ![-7, 0, 29]], ![![0, 1, 0], ![-8, 15, 3], ![-6, 20, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-7, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-7, 1, 0]] 
 ![![29, 0, 0], ![22, 1, 0], ![5, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-7, 1, 0], ![-1, -6, 3], ![197, 20, -8]]]
  hmulB := by decide  
  f := ![![![61, 360, -180], ![0, 1740, 0]], ![![46, 270, -135], ![1, 1305, 0]], ![![11, 62, -31], ![2, 300, 0]]]
  g := ![![![1, 0, 0], ![-22, 29, 0], ![-5, 0, 29]], ![![-1, 1, 0], ![4, -6, 3], ![-7, 20, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![14, 1, 0]] ![![29, 0, 0], ![-7, 1, 0]]
  ![![29, 0, 0], ![-4, -7, 1]] where
 M := ![![![841, 0, 0], ![-203, 29, 0]], ![![406, 29, 0], ![-99, 8, 3]]]
 hmul := by decide  
 g := ![![![![29, 0, 0], ![0, 0, 0]], ![![-3, 8, -1], ![29, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![-3, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-4, -7, 1]] ![![29, 0, 0], ![-7, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-203, 29, 0]], ![![-116, -203, 29], ![232, 58, -29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-7, 1, 0]]], ![![![-4, -7, 1]], ![![8, 2, -1]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![1, 3, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![1, 3, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![1, 3, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![1, 3, 1], ![194, 24, 8], ![453, 119, 19]]]
  hmulB := by decide  
  f := ![![![0, -3, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -3, 31]], ![![0, 0, 1], ![6, 0, 8], ![14, 2, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 30], [0, 1]]
 g := ![![[27, 18], [3, 2], [1, 19], [14, 1]], ![[0, 13], [0, 29], [19, 12], [28, 30]]]
 h' := ![![[14, 30], [5, 24], [12, 8], [13, 22], [0, 1]], ![[0, 1], [0, 7], [0, 23], [11, 9], [14, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [12, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [19, 17, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1155, 737, 132]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33, 11, 132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-8, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-8, 1, 0]] 
 ![![31, 0, 0], ![23, 1, 0], ![12, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-8, 1, 0], ![-1, -7, 3], ![197, 20, -9]]]
  hmulB := by decide  
  f := ![![![-369, -2647, 1134], ![31, -11718, 0]], ![![-271, -1961, 840], ![32, -8680, 0]], ![![-140, -1025, 439], ![23, -4536, 0]]]
  g := ![![![1, 0, 0], ![-23, 31, 0], ![-12, 0, 31]], ![![-1, 1, 0], ![4, -7, 3], ![-5, 20, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![1, 3, 1]] ![![31, 0, 0], ![-8, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-248, 31, 0]], ![![31, 93, 31], ![186, 0, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-8, 1, 0]]], ![![![1, 3, 1]], ![![6, 0, 0]]]]
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


lemma PB276I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB276I0 : PrimesBelowBoundCertificateInterval O 1 31 276 where
  m := 11
  g := ![3, 3, 3, 1, 2, 2, 2, 3, 3, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB276I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N2]
    · exact ![I29N0, I29N1, I29N1]
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
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
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
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
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
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I11N0, I11N1, I13N0, I13N1, I17N1, I19N0, I19N1, I19N2, I23N0, I23N1, I23N2, I29N0, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1, I3N1], [I5N0, I5N0, I5N0], [], [I11N0, I11N1], [I13N0, I13N1], [I17N1], [I19N0, I19N1, I19N2], [I23N0, I23N1, I23N2], [I29N0, I29N1, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
