
import IdealArithmetic.Examples.NF3_1_337635_1.RI3_1_337635_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-392837679362807620739574858, -126114889498405309244503911, -18509199998925595369021985]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-392837679362807620739574858, -126114889498405309244503911, -18509199998925595369021985]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-392837679362807620739574858, -126114889498405309244503911, -18509199998925595369021985], ![-4960465599712059558897891980, -1592486168798897461387353899, -233720578997885023119985837], ![-28838324785860563318629156168, -9258129590794695449928535263, -1358765589801012438267368062]]]
  hmulB := by decide  
  f := ![![![180537431296393, 6036940733427, -3497704638992]], ![![-468692421624928, -8146248515858, 7785793052923]], ![![1277642479904146, -8558212277697, -15932041568781]]]
  g := ![![![-196418839681403810369787429, -126114889498405309244503911, -18509199998925595369021985], ![-2480232799856029779448945990, -1592486168798897461387353899, -233720578997885023119985837], ![-14419162392930281659314578084, -9258129590794695449928535263, -1358765589801012438267368062]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![180537431296393, 6036940733427, -3497704638992]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![180537431296393, 6036940733427, -3497704638992]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 2]] where
  M :=![![![180537431296393, 6036940733427, -3497704638992], ![-937384843249856, -16292497031716, 15571586105846], ![2555284959808292, -17116424555394, -31864083137562]]]
  hmulB := by decide  
  f := ![![![-392837679362807620739574858, -126114889498405309244503911, -18509199998925595369021985]], ![![-2676651639537433589818733419, -859300529148651385315928905, -126114889498405309244503911]], ![![-28838324785860563318629156168, -9258129590794695449928535263, -1358765589801012438267368062]]]
  g := ![![![87250245281483, 6036940733427, -1748852319496], ![-460546173109070, -16292497031716, 7785793052923], ![1286200692181843, -17116424555394, -15932041568781]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![805, 1643, 524]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-419, 1643, 262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-392837679362807620739574858, -126114889498405309244503911, -18509199998925595369021985]] ![![180537431296393, 6036940733427, -3497704638992]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![471005237024942080515, 151209460143742543247, 22192194360726050705]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![471005237024942080515, 151209460143742543247, 22192194360726050705]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![471005237024942080515, 151209460143742543247, 22192194360726050705], ![5947508088674581588940, 1909361970090795564652, 280226725926759035789], ![34576627229848420001256, 11100329096213302832351, 1629135244164036528863]]]
  hmulB := by decide  
  f := ![![![-5295459263, -10600880706, 1895587223]], ![![167573972167, 27815612753, -7067253804]], ![![-1119881441166, -145672061315, 40312080682]]]
  g := ![![![91803796053249145286, 151209460143742543247, 22192194360726050705], ![1159230888910089317570, 1909361970090795564652, 280226725926759035789], ![6739342548435681370393, 11100329096213302832351, 1629135244164036528863]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![471005237024942080515, 151209460143742543247, 22192194360726050705]] ![![471005237024942080515, 151209460143742543247, 22192194360726050705]]
  ![![1888496652417116321110389387349462689238885, 606274701103027041279057773506890378394704, 88979657688608281288433132662097169778373]] where
 M := ![![![1888496652417116321110389387349462689238885, 606274701103027041279057773506890378394704, 88979657688608281288433132662097169778373]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1888496652417116321110389387349462689238885, 606274701103027041279057773506890378394704, 88979657688608281288433132662097169778373]] ![![471005237024942080515, 151209460143742543247, 22192194360726050705]]
  ![![3, 0, 0]] where
 M := ![![![7571931957100075554932628011915053510614285706264957230441436023, 2430859900221499329264044838253051807257717830666242319477507526, 356764155616510108840172604195971471596467481044251618999405280]]]
 hmul := by decide  
 g := ![![![![2523977319033358518310876003971684503538095235421652410147145341, 810286633407166443088014946084350602419239276888747439825835842, 118921385205503369613390868065323823865489160348083872999801760]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-905783, -820108, 153405]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-905783, -820108, 153405]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![-905783, -820108, 153405], ![41112540, 7171599, -1793621], ![-260901484, -31458739, 8965220]]]
  hmulB := by decide  
  f := ![![![7869907882861, 2526520787465, 370803786473]], ![![21449064531525, 6885913814645, 1010608314986]], ![![121842357559460, 39115737280499, 5740805128639]]]
  g := ![![![-139859, -820108, 153405], ![8223085, 7171599, -1793621], ![-53060725, -31458739, 8965220]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-961507, -308678, -45303]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-961507, -308678, -45303]] 
 ![![5, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![-961507, -308678, -45303], ![-12141204, -3897759, -572053], ![-70584500, -22660139, -3325706]]]
  hmulB := by decide  
  f := ![![![2513, -449, 43]], ![![3310, 732, -171]], ![![-25366, -4485, 1117]]]
  g := ![![![-50709, -308678, -45303], ![-640316, -3897759, -572053], ![-3722562, -22660139, -3325706]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-905783, -820108, 153405]] ![![-961507, -308678, -45303]]
  ![![2513, -449, 43]] where
 M := ![![![2513, -449, 43]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![2513, -449, 43]] ![![-961507, -308678, -45303]]
  ![![5, 0, 0]] where
 M := ![![![5, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58613594639, 2666529558, -1257106885]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![58613594639, 2666529558, -1257106885]] 
 ![![7, 0, 0], ![0, 7, 0], ![5, 0, 1]] where
  M :=![![![58613594639, 2666529558, -1257106885], ![-336904645180, -11632075133, 6590166001], ![1051534566724, 22662491439, -18222241134]]]
  hmulB := by decide  
  f := ![![![8944699626154250769, 2871567225370568751, 421444385323080979]], ![![112947095266585702372, 36260041200263516302, 5321690065418056523]], ![![100193774180499710963, 32165770808181333444, 4720796151637266382]]]
  g := ![![![9271304152, 380932794, -1257106885], ![-52836496455, -1661725019, 6590166001], ![163235110342, 3237498777, -18222241134]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6], [0, 1]]
 g := ![![[2, 4], [1, 1]], ![[6, 3], [2, 6]]]
 h' := ![![[1, 6], [4, 5], [0, 1]], ![[0, 1], [2, 2], [1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2146, 2149, 954]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-988, 307, 954]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8944699626154250769, 2871567225370568751, 421444385323080979]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![8944699626154250769, 2871567225370568751, 421444385323080979]] 
 ![![7, 0, 0], ![1, 1, 0], ![6, 0, 1]] where
  M :=![![![8944699626154250769, 2871567225370568751, 421444385323080979], ![112947095266585702372, 36260041200263516302, 5321690065418056523], ![656632921132726722896, 210802559530416490353, 30938351134845459779]]]
  hmulB := by decide  
  f := ![![![58613594639, 2666529558, -1257106885]], ![![-39755864363, -1280792225, 761865588]], ![![200459447794, 5523095541, -3680697492]]]
  g := ![![![506352298406456592, 2871567225370568751, 421444385323080979], ![6393844810544835276, 36260041200263516302, 5321690065418056523], ![37171464970462496267, 210802559530416490353, 30938351134845459779]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![58613594639, 2666529558, -1257106885]] ![![8944699626154250769, 2871567225370568751, 421444385323080979]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![162182192687, 52066261420, 7641483489]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![162182192687, 52066261420, 7641483489]] 
 ![![11, 0, 0], ![0, 11, 0], ![10, 4, 1]] where
  M :=![![![162182192687, 52066261420, 7641483489], ![2047917575052, 657454496469, 96491039351], ![11905840485508, 3822198928705, 560963457118]]]
  hmulB := by decide  
  f := ![![![-3141283, -194165, 76189]], ![![20418652, 1083514, -464519]], ![![-2017554, -79029, 41077]]]
  g := ![![![7797032527, 1954575224, 7641483489], ![98455198322, 24680939915, 96491039351], ![572382355848, 143485918203, 560963457118]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [7, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[10, 4], [3, 5], [1]], ![[5, 7], [5, 6], [1]]]
 h' := ![![[7, 10], [1, 2], [4, 7], [0, 1]], ![[0, 1], [4, 9], [9, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [7, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3579, 105, 183]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![159, -57, 183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3141283, 194165, -76189]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![3141283, 194165, -76189]] 
 ![![11, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![3141283, 194165, -76189], ![-20418652, -1083514, 464519], ![72454872, 3261725, -1548033]]]
  hmulB := by decide  
  f := ![![![-162182192687, -52066261420, -7641483489]], ![![-245149667800, -78701776559, -11550633937]], ![![-1097092970745, -352205926375, -51691358237]]]
  g := ![![![221892, 194165, -76189], ![-1504465, -1083514, 464519], ![5541455, 3261725, -1548033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![162182192687, 52066261420, 7641483489]] ![![3141283, 194165, -76189]]
  ![![11, 0, 0]] where
 M := ![![![-11, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [11, 11, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 12, 8], [1, 0, 5], [0, 1]]
 g := ![![[1, 10, 12], [0, 9], [1]], ![[8, 8], [3, 9], [0, 4, 5, 5]], ![[2, 2, 9, 8], [6, 10], [7, 7, 11, 8]]]
 h' := ![![[2, 12, 8], [4, 0, 8], [2, 2, 3], [0, 1]], ![[1, 0, 5], [5, 12], [8, 9, 3], [2, 12, 8]], ![[0, 1], [3, 1, 5], [2, 2, 7], [1, 0, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 10], []]
 b := ![[], [1, 5, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [11, 11, 10, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3918395, -1992302, -399321]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-301415, -153254, -30717]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [10, 2, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 2, 1], [13, 14, 16], [0, 1]]
 g := ![![[16, 5, 13], [], [6, 1], []], ![[5, 7, 12, 4], [12, 8], [11, 9], [10, 1]], ![[6, 13, 15, 15], [11, 8], [1, 4], [12, 1]]]
 h' := ![![[10, 2, 1], [13, 5, 8], [8, 12], [0, 0, 1], [0, 1]], ![[13, 14, 16], [12, 5, 15], [9, 7, 12], [0, 10, 14], [10, 2, 1]], ![[0, 1], [11, 7, 11], [11, 15, 5], [15, 7, 2], [13, 14, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 4], []]
 b := ![[], [11, 10, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [10, 2, 11, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1172490, -500174, -90491]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68970, -29422, -5323]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1937333596663037, -131115352114802, 48943579022189]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-1937333596663037, -131115352114802, 48943579022189]] 
 ![![19, 0, 0], ![0, 19, 0], ![11, 17, 1]] where
  M :=![![![-1937333596663037, -131115352114802, 48943579022189], ![13116879177946652, 770278634509123, -311174283251793], ![-48255793544713588, -2465614625328671, 1081452917760916]]]
  hmulB := by decide  
  f := ![![![-3462326998263048831297883135, -1111530308145462003804936727, -163133289496256499982547881]], ![![-43719721584996741995322832108, -14035588097191387834090596960, -2059927326794667507627325573]], ![![-54499540259148696109956056371, -17496293911126179154749911052, -2567836395282362602943991201]]]
  g := ![![![-130300682416164, -50692431341685, 48943579022189], ![870515594406125, 318960076304716, -311174283251793], ![-3165882928425456, -1097384959329697, 1081452917760916]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [10, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18], [0, 1]]
 g := ![![[15, 4], [13, 17], [4], [1]], ![[4, 15], [9, 2], [4], [1]]]
 h' := ![![[2, 18], [3, 17], [3, 6], [9, 2], [0, 1]], ![[0, 1], [18, 2], [15, 13], [13, 17], [2, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [1, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [10, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106960, 95805, 26378]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9642, -18559, 26378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3462326998263048831297883135, -1111530308145462003804936727, -163133289496256499982547881]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-3462326998263048831297883135, -1111530308145462003804936727, -163133289496256499982547881]] 
 ![![19, 0, 0], ![5, 1, 0], ![4, 0, 1]] where
  M :=![![![-3462326998263048831297883135, -1111530308145462003804936727, -163133289496256499982547881], ![-43719721584996741995322832108, -14035588097191387834090596960, -2059927326794667507627325573], ![-254170400997987075024400210728, -81597753269543728718853857671, -11975660770396720326463271387]]]
  hmulB := by decide  
  f := ![![![-1937333596663037, -131115352114802, 48943579022189]], ![![180537431296393, 6036940733427, -3497704638992]], ![![-2947638312177144, -157372422830941, 67222485992088]]]
  g := ![![![144624089497330904613525896, -1111530308145462003804936727, -163133289496256499982547881], ![1826206747796782484507339736, -14035588097191387834090596960, -2059927326794667507627325573], ![10616895180595707888195903325, -81597753269543728718853857671, -11975660770396720326463271387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-1937333596663037, -131115352114802, 48943579022189]] ![![-3462326998263048831297883135, -1111530308145462003804936727, -163133289496256499982547881]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49157838041137055309267461, -15781417206705587439681002, -2316153219553770290032232]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-49157838041137055309267461, -15781417206705587439681002, -2316153219553770290032232]] 
 ![![23, 0, 0], ![0, 23, 0], ![12, 4, 1]] where
  M :=![![![-49157838041137055309267461, -15781417206705587439681002, -2316153219553770290032232], ![-620729062840410437728638176, -199276141981961319570817919, -29246681193857404589329772], ![-3608690748556686996105870360, -1158518286042069951954882476, -170029460788103914981488147]]]
  hmulB := by decide  
  f := ![![![-17292727210027, 824396178994, 93758772768]], ![![25127351101824, -11030322210489, 1555033585220]], ![![3861195771980, 1018744122968, -227831138331]]]
  g := ![![![-928869539412687470820899, -283339318630022012154438, -2316153219553770290032232], ![-11729082109309634028551344, -3577800748110073965804297, -29246681193857404589329772], ![-68188574743453913753391852, -20800019256071925740388256, -170029460788103914981488147]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [14, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 22], [0, 1]]
 g := ![![[14, 4], [3, 9], [11, 6], [1]], ![[12, 19], [10, 14], [8, 17], [1]]]
 h' := ![![[11, 22], [4, 2], [7, 3], [9, 11], [0, 1]], ![[0, 1], [3, 21], [17, 20], [15, 12], [11, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [14, 12, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![807, 361, 73]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 3, 73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17292727210027, 824396178994, 93758772768]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-17292727210027, 824396178994, 93758772768]] 
 ![![23, 0, 0], ![16, 1, 0], ![2, 0, 1]] where
  M :=![![![-17292727210027, 824396178994, 93758772768], ![25127351101824, -11030322210489, 1555033585220], ![195810824868568, 57659649522292, -12585355795709]]]
  hmulB := by decide  
  f := ![![![-49157838041137055309267461, -15781417206705587439681002, -2316153219553770290032232]], ![![-61184977021678405333779024, -19642557273445683417639737, -2882831856813814314341108]], ![![-161174192375607004640191534, -51742657411107875079749760, -7593989879443976328763157]]]
  g := ![![![-1333503635629, 824396178994, 93758772768], ![8630540839096, -11030322210489, 1555033585220], ![-30503167647682, 57659649522292, -12585355795709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-49157838041137055309267461, -15781417206705587439681002, -2316153219553770290032232]] ![![-17292727210027, 824396178994, 93758772768]]
  ![![23, 0, 0]] where
 M := ![![![23, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![138279470355640891417085, 44392636042668598163410, 6515267009797885914579]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![138279470355640891417085, 44392636042668598163410, 6515267009797885914579]] 
 ![![29, 0, 0], ![0, 29, 0], ![2, 24, 1]] where
  M :=![![![138279470355640891417085, 44392636042668598163410, 6515267009797885914579], ![1746091558625833425107172, 560557592966586872626077, 82270005075539310412241], ![10151134900809350882686708, 3258875926503556714508575, 478287587891047562213836]]]
  hmulB := by decide  
  f := ![![![1753109114993, 182728347385, -55311985337]], ![![-14823612070316, -1272257687168, 420768680107]], ![![-9947091803038, -875111796873, 286027516711]]]
  g := ![![![4318928839173969640963, -3861164558361402199534, 6515267009797885914579], ![54536260292232924285610, -48755949270564019905783, 82270005075539310412241], ![317053783621629508905484, -283449178720054647538741, 478287587891047562213836]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [11, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 28], [0, 1]]
 g := ![![[16, 5], [9], [0, 20], [27, 1]], ![[6, 24], [9], [18, 9], [25, 28]]]
 h' := ![![[27, 28], [17, 11], [0, 3], [22, 22], [0, 1]], ![[0, 1], [24, 18], [23, 26], [7, 7], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [16, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [11, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1351, 4380, 1473]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55, -1068, 1473]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1753109114993, 182728347385, -55311985337]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![1753109114993, 182728347385, -55311985337]] 
 ![![29, 0, 0], ![11, 1, 0], ![21, 0, 1]] where
  M :=![![![1753109114993, 182728347385, -55311985337], ![-14823612070316, -1272257687168, 420768680107], ![63794809169496, 4790485687945, -1693026367275]]]
  hmulB := by decide  
  f := ![![![138279470355640891417085, 44392636042668598163410, 6515267009797885914579]], ![![112660887328892525196383, 36168158256411774221503, 5308204902872967430090]], ![![450172544078545158705017, 144521423565503354342765, 21210627417131143669655]]]
  g := ![![![31194792615, 182728347385, -55311985337], ![-333273096335, -1272257687168, 420768680107], ![1608724838444, 4790485687945, -1693026367275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![138279470355640891417085, 44392636042668598163410, 6515267009797885914579]] ![![1753109114993, 182728347385, -55311985337]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6814419887788877414779292982021135, 2187671540413835597367904735427121, 321072715795301339866323871513435]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![6814419887788877414779292982021135, 2187671540413835597367904735427121, 321072715795301339866323871513435]] 
 ![![31, 0, 0], ![0, 31, 0], ![21, 15, 1]] where
  M :=![![![6814419887788877414779292982021135, 2187671540413835597367904735427121, 321072715795301339866323871513435], ![86047487833140759084174797565600580, 27624308944330190724393982265227486, 4054270365032369854869485599340807], ![500248484997767181010423671528867848, 160597584502509105333302481163683693, 23570038579297820869524496665886679]]]
  hmulB := by decide  
  f := ![![![-262770267897525847, 5491537299699816, 2634878445469427]], ![![706147423385806436, -104455780760599265, 8348196153930205]], ![![188374848318477355, -27623968643819796, 2185529443525212]]]
  g := ![![![2319124389920944438273925169000, -84787716016634983891192043137884, 321072715795301339866323871513435], ![29284198950354584900503225143343, -1070636984875979261246719410480149, 4054270365032369854869485599340807], ![170247575242352991948685211137019, -6224290135063167990631128026600532, 23570038579297820869524496665886679]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 14, 1] where
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
 g := ![![[4, 18], [28, 2], [30, 19], [17, 1]], ![[0, 13], [0, 29], [12, 12], [3, 30]]]
 h' := ![![[17, 30], [26, 24], [19, 8], [18, 22], [0, 1]], ![[0, 1], [0, 7], [0, 23], [20, 9], [17, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [19, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [19, 14, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16131, 9268, 2048]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-867, -692, 2048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1348818469716955290899649433805, -433018778997162977078461828006, -63551823386011824552518530017]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-1348818469716955290899649433805, -433018778997162977078461828006, -63551823386011824552518530017]] 
 ![![31, 0, 0], ![2, 1, 0], ![28, 0, 1]] where
  M :=![![![-1348818469716955290899649433805, -433018778997162977078461828006, -63551823386011824552518530017], ![-17031888667451168980074966044556, -5467843005102804092024186002797, -802485734608314129604405125995], ![-99017144103788508876952803861052, -31788030637366694248565231676133, -4665357270494489962419780876802]]]
  hmulB := by decide  
  f := ![![![-36611929385037859, -3342203783667449, 1073621040841579]], ![![6919567102434434, 504241278476496, -180993113757849]], ![![-71244357282241276, -5635461809904349, 1939848546833773]]]
  g := ![![![41828069131796830668638485893, -433018778997162977078461828006, -63551823386011824552518530017], ![528174126186684994609572564158, -5467843005102804092024186002797, -802485734608314129604405125995], ![3070610346606148340901016904570, -31788030637366694248565231676133, -4665357270494489962419780876802]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![6814419887788877414779292982021135, 2187671540413835597367904735427121, 321072715795301339866323871513435]] ![![-1348818469716955290899649433805, -433018778997162977078461828006, -63551823386011824552518530017]]
  ![![31, 0, 0]] where
 M := ![![![-78243296890034114067637156123122219609680952298071224714561505571, -25118885635622159735728463328614868674996417583551170634600911102, -3686562941370604458015116910025038539830163970790600062993854560]]]
 hmul := by decide  
 g := ![![![![-2523977319033358518310876003971684503538095235421652410147145341, -810286633407166443088014946084350602419239276888747439825835842, -118921385205503369613390868065323823865489160348083872999801760]]]]
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


lemma PB165I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB165I0 : PrimesBelowBoundCertificateInterval O 1 31 165 where
  m := 11
  g := ![2, 3, 3, 2, 2, 1, 1, 2, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB165I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I19N1, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1, I5N1], [I7N0, I7N1], [I11N0, I11N1], [], [], [I19N1], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
