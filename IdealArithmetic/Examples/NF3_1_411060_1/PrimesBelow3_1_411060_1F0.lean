
import IdealArithmetic.Examples.NF3_1_411060_1.RI3_1_411060_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, -2, 5], ![114, -18, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 3], ![0, -1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, -2, 5], ![57, -18, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39232723, 7645813, -10247180]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![39232723, 7645813, -10247180]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![39232723, 7645813, -10247180], ![-1168178520, 208390337, 7487525], ![-296555838, -260590794, 215877862]]]
  hmulB := by decide  
  f := ![![![46938040497864344, 1019759008769114, 2192661509482485]], ![![148450726289433817, 3225187159205250, 6934720540887755]], ![![206576989789273315, 4488017482357441, 9650028195708448]]]
  g := ![![![20917045, 7645813, -10247180], ![-692028191, 208390337, 7487525], ![-125921453, -260590794, 215877862]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![-46938040497864344, -1019759008769114, -2192661509482485]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, -2, 5]]]
 hmul := by decide  
 g := ![![![![-78465446, -15291626, 20494360]], ![![1168178520, -208390337, -7487525]]], ![![![1168178520, -208390337, -7487525]], ![![-426788925, 859867322, -532207130]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-46938040497864344, -1019759008769114, -2192661509482485]] ![![39232723, 7645813, -10247180]]
  ![![2, 0, 0]] where
 M := ![![![-2, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40311716120646243601953823519185668521215, -875797865376219313902706005366258649279, -1883119691009412989251949682157190746021]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-40311716120646243601953823519185668521215, -875797865376219313902706005366258649279, -1883119691009412989251949682157190746021]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![-40311716120646243601953823519185668521215, -875797865376219313902706005366258649279, -1883119691009412989251949682157190746021], ![-214675644775073080774722263765919745046394, -4663965951724371167613317229623717794279, -10028348399909335537269379073302865484458], ![-314516601427962082559630748377673231064200, -6833074715341008220774688089293633265230, -14692314351633706704882696302926583278737]]]
  hmulB := by decide  
  f := ![![![71138818222875849717, -33310689365079069207, 13618568471568408077]], ![![517505601919599506926, -35791345178399119085, -41899247136896707268]], ![![-748300593953405122940, 254338410076748047550, -77690592315295826353]]]
  g := ![![![-13437238706882081200651274506395222840405, -875797865376219313902706005366258649279, -1883119691009412989251949682157190746021], ![-71558548258357693591574087921973248348798, -4663965951724371167613317229623717794279, -10028348399909335537269379073302865484458], ![-104838867142654027519876916125891077021400, -6833074715341008220774688089293633265230, -14692314351633706704882696302926583278737]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1841, -40, -86]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-1841, -40, -86]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![-1841, -40, -86], ![-9804, -213, -458], ![-14364, -312, -671]]]
  hmulB := by decide  
  f := ![![![-27, 8, -2]], ![![-94, 3, 10]], ![![228, -56, 9]]]
  g := ![![![-587, -40, -86], ![-3126, -213, -458], ![-4580, -312, -671]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-40311716120646243601953823519185668521215, -875797865376219313902706005366258649279, -1883119691009412989251949682157190746021]] ![![-40311716120646243601953823519185668521215, -875797865376219313902706005366258649279, -1883119691009412989251949682157190746021]]
  ![![2405319333332197421861658078290949938305642540658116307494170606996261592280274351, 52257103899418872174684840573778068379274824988509922038723234233566824849778656, 112361978989121777046655166291841133006674466310149206530391420099610471979396774]] where
 M := ![![![2405319333332197421861658078290949938305642540658116307494170606996261592280274351, 52257103899418872174684840573778068379274824988509922038723234233566824849778656, 112361978989121777046655166291841133006674466310149206530391420099610471979396774]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![2405319333332197421861658078290949938305642540658116307494170606996261592280274351, 52257103899418872174684840573778068379274824988509922038723234233566824849778656, 112361978989121777046655166291841133006674466310149206530391420099610471979396774]] ![![-1841, -40, -86]]
  ![![3, 0, 0]] where
 M := ![![![-6554489005494223281946077507734965053318970335617926600366953034216811561727270285351, -142400473908470111086230606056907159595093672837643818131496996242678664641785621256, -306186104154203534134413868297637450259471695235445664320126556367490729415477453988]]]
 hmul := by decide  
 g := ![![![![-2184829668498074427315359169244988351106323445205975533455651011405603853909090095117, -47466824636156703695410202018969053198364557612547939377165665414226221547261873752, -102062034718067844711471289432545816753157231745148554773375518789163576471825817996]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71828215, 1560514, 3355380]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![71828215, 1560514, 3355380]] 
 ![![5, 0, 0], ![0, 1, 0], ![3, 0, 1]] where
  M :=![![![71828215, 1560514, 3355380], ![382513320, 8310347, 17868710], ![560411916, 12175308, 26179057]]]
  hmulB := by decide  
  f := ![![![-9901, 1742, 80]], ![![1824, -2965, 1790]], ![![35601, -5034, -1127]]]
  g := ![![![12352415, 1560514, 3355380], ![65781438, 8310347, 17868710], ![96374949, 12175308, 26179057]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![10, 0, 1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![10, 0, 1]] 
 ![![5, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![10, 0, 1], ![114, -8, 3], ![114, 12, -5]]]
  hmulB := by decide  
  f := ![![![15, -8, -7], ![50, -5, 0]], ![![4, -3, -3], ![21, -2, 0]], ![![-2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![0, 0, 5]], ![![2, 0, 1], ![26, -8, 3], ![18, 12, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![71828215, 1560514, 3355380]] ![![5, 0, 0], ![10, 0, 1]]
  ![![5, 0, 0], ![13, -1, 1]] where
 M := ![![![359141075, 7802570, 16776900], ![1278694066, 27780448, 59732857]]]
 hmul := by decide  
 g := ![![![![9775653, 6333788, -1417894], ![23866370, 0, 0]], ![![34805459, 22550963, -5048302], ![84974367, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![13, -1, 1]] ![![5, 0, 0], ![10, 0, 1]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![50, 0, 5]], ![![65, -5, 5], ![130, 20, 5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![10, 0, 1]]], ![![![13, -1, 1]], ![![26, 4, 1]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 5, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 4], [2, 2], [0, 1]]
 g := ![![[6, 5, 1], [1]], ![[2, 5, 2], [1]], ![[6, 4, 4], [1]]]
 h' := ![![[6, 4], [1, 2, 1], [0, 1]], ![[2, 2], [0, 0, 2], [6, 4]], ![[0, 1], [2, 5, 4], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3], []]
 b := ![[], [3, 3, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 5, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-857388, 396753, -172123]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-122484, 56679, -24589]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![6, 1, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![6, 1, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![6, 1, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![6, 1, 1], ![114, -14, 8], ![228, -6, -6]]]
  hmulB := by decide  
  f := ![![![-5, -1, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -1, 11]], ![![0, 0, 1], ![6, -2, 8], ![24, 0, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10], [0, 1]]
 g := ![![[3, 1], [0, 9], [1]], ![[6, 10], [5, 2], [1]]]
 h' := ![![[3, 10], [0, 10], [1, 3], [0, 1]], ![[0, 1], [8, 1], [10, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [7, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [10, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1029, 2212, -1297]
  a := ![-1, -4, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![801, 319, -1297]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![3, 1, 0]] 
 ![![11, 0, 0], ![3, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![3, 1, 0], ![0, 1, 5], ![114, -18, 6]]]
  hmulB := by decide  
  f := ![![![7, 2, 0], ![-22, 0, 0]], ![![3, 1, 0], ![-10, 0, 0]], ![![6, 1, -4], ![-20, 9, 0]]]
  g := ![![![1, 0, 0], ![-3, 11, 0], ![-6, 0, 11]], ![![0, 1, 0], ![-3, 1, 5], ![12, -18, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![6, 1, 1]] ![![11, 0, 0], ![3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![33, 11, 0]], ![![66, 11, 11], ![132, -11, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![3, 1, 0]]], ![![![6, 1, 1]], ![![12, -1, 1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![3, 1, 0]] 
 ![![13, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![3, 1, 0], ![0, 1, 5], ![114, -18, 6]]]
  hmulB := by decide  
  f := ![![![22, 7, 0], ![-91, 0, 0]], ![![6, 2, 0], ![-25, 0, 0]], ![![2, 0, -3], ![-8, 8, 0]]]
  g := ![![![1, 0, 0], ![-3, 13, 0], ![-2, 0, 13]], ![![0, 1, 0], ![-1, 1, 5], ![12, -18, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17404140226348365068348120791509316331036321423, 378116099382273915906450895389390536920928150, 813016222560167744568815819919752775174964472]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![17404140226348365068348120791509316331036321423, 378116099382273915906450895389390536920928150, 813016222560167744568815819919752775174964472]] 
 ![![13, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![17404140226348365068348120791509316331036321423, 378116099382273915906450895389390536920928150, 813016222560167744568815819919752775174964472], ![92683849371859122880845003470851816369945949808, 2013616021500797834296534242174985304045104627, 4329629164591872813238701936706211010129534166], ![135789084701438349294180405545242337578931758908, 2950104881841082448509673722028003637522866964, 6343245186092670647535236178881196314174638793]]]
  hmulB := by decide  
  f := ![![![-33139225644550492696813, -26965864239022273219942, 22653218675015608360956]], ![![183356275006498184382162, -42212355288532348928753, 5311511298463777626838]], ![![-45466097786954713231911, 52025122129655492202354, -29682726343215739437547]]]
  g := ![![![976645766336478333784843689185670367998912239, 378116099382273915906450895389390536920928150, 813016222560167744568815819919752775174964472], ![5201020442236824418103822477514097808868209196, 2013616021500797834296534242174985304045104627, 4329629164591872813238701936706211010129534166], ![7619901527085680204655127282802363600866972365, 2950104881841082448509673722028003637522866964, 6343245186092670647535236178881196314174638793]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![3, 1, 0]] ![![13, 0, 0], ![3, 1, 0]]
  ![![33139225644550492696813, 26965864239022273219942, -22653218675015608360956]] where
 M := ![![![169, 0, 0], ![39, 13, 0]], ![![39, 13, 0], ![9, 4, 5]]]
 hmul := by decide  
 g := ![![![![-226253822942528745888525570289621112303472178499, -4915509291969560906783861640062076979972065950, -10569210893282180679394605658956786077274538136]], ![![-144896270050904218085889365845379765363054914077, -3147964319647619582015886928343156914807889077, -6768677832272376046945149396465469335654427582]]], ![![![-144896270050904218085889365845379765363054914077, -3147964319647619582015886928343156914807889077, -6768677832272376046945149396465469335654427582]], ![![-92793698694751040277647317594861753873366883583, -2016002568434543755607120279795728787391008206, -4334760660913258014750025463116046199074308529]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![33139225644550492696813, 26965864239022273219942, -22653218675015608360956]] ![![17404140226348365068348120791509316331036321423, 378116099382273915906450895389390536920928150, 813016222560167744568815819919752775174964472]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1405466072292392453173, -30534651074850931570, -65654878791526733190]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-1405466072292392453173, -30534651074850931570, -65654878791526733190]] 
 ![![17, 0, 0], ![4, 1, 0], ![12, 0, 1]] where
  M :=![![![-1405466072292392453173, -30534651074850931570, -65654878791526733190], ![-7484656182234047583660, -162608951895209392613, -349637891748834857420], ![-10965606404767053782640, -238234826151004030020, -512246843644044250033]]]
  hmulB := by decide  
  f := ![![![-64935457829, 16762878010, -3118823930]], ![![-36193397608, 1454654643, 3646036620]], ![![45658627716, -8117832660, -311197177]]]
  g := ![![![-29145230734980466389, -30534651074850931570, -65654878791526733190], ![-155209745509834807304, -162608951895209392613, -349637891748834857420], ![-227394410378500391892, -238234826151004030020, -512246843644044250033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![6, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![6, 1, 0]] 
 ![![17, 0, 0], ![6, 1, 0], ![2, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![6, 1, 0], ![0, 4, 5], ![114, -18, 9]]]
  hmulB := by decide  
  f := ![![![7, 1, 0], ![-17, 0, 0]], ![![-6, -1, 0], ![18, 0, 0]], ![![-2, -2, -2], ![6, 7, 0]]]
  g := ![![![1, 0, 0], ![-6, 17, 0], ![-2, 0, 17]], ![![0, 1, 0], ![-2, 4, 5], ![12, -18, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-1405466072292392453173, -30534651074850931570, -65654878791526733190]] ![![17, 0, 0], ![6, 1, 0]]
  ![![17, 0, 0], ![15, 5, 1]] where
 M := ![![![-23892923228970671703941, -519089068272465836690, -1116132939455954464230], ![-15917452615988402302698, -345816858344314982033, -743567164497995256560]]]
 hmul := by decide  
 g := ![![![![-813790538443735003498, 166690526874701551655, -26209843201616236545], ![-670565605028478442965, 0, 0]], ![![-542146819411007970909, 111049139430751408846, -17460983456739851181], ![-446730445733417786483, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![15, 5, 1]] ![![17, 0, 0], ![6, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![102, 17, 0]], ![![255, 85, 17], ![204, 17, 34]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![6, 1, 0]]], ![![![15, 5, 1]], ![![12, 1, 2]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![0, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![0, 1, 0]] 
 ![![19, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![0, -2, 5], ![114, -18, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![8, 4, 0]]]
  g := ![![![1, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![0, -2, 5], ![6, -18, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29055961331852330931511, 631259379648615525795, 1357318868823738251169]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![29055961331852330931511, 631259379648615525795, 1357318868823738251169]] 
 ![![19, 0, 0], ![5, 1, 0], ![16, 0, 1]] where
  M :=![![![29055961331852330931511, 631259379648615525795, 1357318868823738251169], ![154734351045906160633266, 3361702933727811358879, 7228253504714292382482], ![226697920325848330573896, 4925157592209779549718, 10589956438442103741361]]]
  hmulB := by decide  
  f := ![![![367975654243, -76096786653, 4776843639]], ![![125496760319, 2826426778, -18014167587]], ![![-118045422932, 11027141946, 7603270417]]]
  g := ![![![220134870127865330728, 631259379648615525795, 1357318868823738251169], ![1172304226412548722061, 3361702933727811358879, 7228253504714292382482], ![1717517334196093313870, 4925157592209779549718, 10589956438442103741361]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-6, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-6, 1, 0]] 
 ![![19, 0, 0], ![13, 1, 0], ![17, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-6, 1, 0], ![0, -8, 5], ![114, -18, -3]]]
  hmulB := by decide  
  f := ![![![109, -18, 0], ![342, 0, 0]], ![![79, -13, 0], ![248, 0, 0]], ![![95, -14, -1], ![298, 4, 0]]]
  g := ![![![1, 0, 0], ![-13, 19, 0], ![-17, 0, 19]], ![![-1, 1, 0], ![1, -8, 5], ![21, -18, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![0, 1, 0]] ![![29055961331852330931511, 631259379648615525795, 1357318868823738251169]]
  ![![19, 0, 0], ![19, -7, 1]] where
 M := ![![![552063265305194287698709, 11993928213323694990105, 25789058507651026772211]], ![![154734351045906160633266, 3361702933727811358879, 7228253504714292382482]]]
 hmul := by decide  
 g := ![![![![15544259775099640998714, 5609254690031185501036, 646176681626228254706], ![13511701556752689932797, 0, 0]]], ![![![4356803105635646262304, 1572182825519752319571, 181112810389868901988], ![3787110107306783244710, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![19, -7, 1]] ![![19, 0, 0], ![-6, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-114, 19, 0]], ![![361, -133, 19], ![0, 57, -38]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-6, 1, 0]]], ![![![19, -7, 1]], ![![0, 3, -2]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![2, -3, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![2, -3, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![2, 20, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![2, -3, 1], ![114, -10, -12], ![-228, 66, -22]]]
  hmulB := by decide  
  f := ![![![-1, 3, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -20, 23]], ![![0, -1, 1], ![6, 10, -12], ![-8, 22, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [22, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22], [0, 1]]
 g := ![![[22, 9], [14, 2], [20, 1], [1]], ![[13, 14], [12, 21], [19, 22], [1]]]
 h' := ![![[22, 22], [14, 20], [20, 5], [1, 22], [0, 1]], ![[0, 1], [17, 3], [15, 18], [2, 1], [22, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [9, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [22, 1, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4054, -9, 187]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![160, -163, 187]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-11, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-11, 1, 0]] 
 ![![23, 0, 0], ![12, 1, 0], ![22, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-11, 1, 0], ![0, -13, 5], ![114, -18, -8]]]
  hmulB := by decide  
  f := ![![![254, -23, 0], ![529, 0, 0]], ![![144, -13, 0], ![300, 0, 0]], ![![242, -14, -3], ![504, 14, 0]]]
  g := ![![![1, 0, 0], ![-12, 23, 0], ![-22, 0, 23]], ![![-1, 1, 0], ![2, -13, 5], ![22, -18, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![2, -3, 1]] ![![23, 0, 0], ![-11, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-253, 23, 0]], ![![46, -69, 23], ![92, 23, -23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-11, 1, 0]]], ![![![2, -3, 1]], ![![4, 1, -1]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![15, -13, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![15, -13, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![15, 16, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![15, -13, 1], ![114, 23, -62], ![-1368, 246, -39]]]
  hmulB := by decide  
  f := ![![![-14, 13, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -16, 29]], ![![0, -1, 1], ![36, 35, -62], ![-27, 30, -39]]]
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
  c := ![2769, 3928, -2611]
  a := ![1, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1446, 1576, -2611]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![4, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![4, 1, 0]] 
 ![![29, 0, 0], ![4, 1, 0], ![10, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![4, 1, 0], ![0, 2, 5], ![114, -18, 7]]]
  hmulB := by decide  
  f := ![![![81, 20, 0], ![-580, 0, 0]], ![![4, 1, 0], ![-28, 0, 0]], ![![26, 6, -1], ![-186, 6, 0]]]
  g := ![![![1, 0, 0], ![-4, 29, 0], ![-10, 0, 29]], ![![0, 1, 0], ![-2, 2, 5], ![4, -18, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![15, -13, 1]] ![![29, 0, 0], ![4, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![116, 29, 0]], ![![435, -377, 29], ![174, -29, -58]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![4, 1, 0]]], ![![![15, -13, 1]], ![![6, -1, -2]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6150789975354420242166467, -133629853779256381924898, -287327725844967750218182]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-6150789975354420242166467, -133629853779256381924898, -287327725844967750218182]] 
 ![![31, 0, 0], ![7, 1, 0], ![24, 0, 1]] where
  M :=![![![-6150789975354420242166467, -133629853779256381924898, -287327725844967750218182], ![-32755360746326323524872748, -711631202586487974389395, -1530132446431185160279036], ![-47989164077161551064311120, -1042595342112998127970020, -2241763649017673134668431]]]
  hmulB := by decide  
  f := ![![![5316434811475, -1494981408602, 339001141562]], ![![2447134639303, -266467509021, -131770826690]], ![![-135074676360, -158124992028, 125241963217]]]
  g := ![![![54209174883212917307877, -133629853779256381924898, -287327725844967750218182], ![288685044713791488469351, -711631202586487974389395, -1530132446431185160279036], ![422946157872696485920044, -1042595342112998127970020, -2241763649017673134668431]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-4, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-4, 1, 0]] 
 ![![31, 0, 0], ![27, 1, 0], ![20, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-4, 1, 0], ![0, -6, 5], ![114, -18, -1]]]
  hmulB := by decide  
  f := ![![![65, -16, 0], ![496, 0, 0]], ![![61, -15, 0], ![466, 0, 0]], ![![44, -6, -4], ![336, 25, 0]]]
  g := ![![![1, 0, 0], ![-27, 31, 0], ![-20, 0, 31]], ![![-1, 1, 0], ![2, -6, 5], ![20, -18, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-6150789975354420242166467, -133629853779256381924898, -287327725844967750218182]] ![![31, 0, 0], ![-4, 1, 0]]
  ![![31, 0, 0], ![13, -6, 1]] where
 M := ![![![-190674489235987027507160477, -4142525467156947839671838, -8907159501194000256763642], ![-8152200844908642556206880, -177111787469462446689803, -380821543051314159406308]]]
 hmul := by decide  
 g := ![![![![-5265789428931027265397990, -542091644436206986587272, -219250760735475982774453], ![-2110385918394244790755599, 0, 0]], ![![-225136425977327480384336, -23176881078838599981941, -9373966302867477439180], ![-90228587662422358791728, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![13, -6, 1]] ![![31, 0, 0], ![-4, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-124, 31, 0]], ![![403, -186, 31], ![62, 31, -31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-4, 1, 0]]], ![![![13, -6, 1]], ![![2, 1, -1]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB182I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB182I0 : PrimesBelowBoundCertificateInterval O 1 31 182 where
  m := 11
  g := ![3, 3, 3, 1, 2, 3, 3, 3, 2, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB182I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N1]
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
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![529, 23]
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
      exact NI5N1
      exact NI5N1
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
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I11N0, I11N1, I13N0, I13N1, I17N0, I17N1, I19N0, I19N1, I19N2, I23N1, I29N1, I31N0, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N0, I3N1], [I5N0, I5N1, I5N1], [], [I11N0, I11N1], [I13N0, I13N0, I13N1], [I17N0, I17N1, I17N1], [I19N0, I19N1, I19N2], [I23N1], [I29N1], [I31N0, I31N1, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
