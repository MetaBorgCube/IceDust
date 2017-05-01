module neverwinter2

model

  entity Character extends AbilityScores, Ratings, Stats {
    name : String
    
    baseStrength     : Int
    baseConstitution : Int
    baseDexterity    : Int
    baseIntelligence : Int
    baseWisdom       : Int
    baseCharisma     : Int
    
    levelStrength     : Int = 0 (default)
    levelConstitution : Int = 0 (default)
    levelDexterity    : Int = 0 (default)
    levelIntelligence : Int = 0 (default)
    levelWisdom       : Int = 0 (default)
    levelCharisma     : Int = 0 (default)
    
    raceStrength     : Int = 0 (default)
    raceConstitution : Int = 0 (default)
    raceDexterity    : Int = 0 (default)
    raceIntelligence : Int = 0 (default)
    raceWisdom       : Int = 0 (default)
    raceCharisma     : Int = 0 (default)
    
    strength     : Int = baseStrength     + 2 + levelStrength     + raceStrength     + sum(items.strength)
    constitution : Int = baseConstitution + 2 + levelConstitution + raceConstitution + sum(items.constitution)
    dexterity    : Int = baseDexterity    + 2 + levelDexterity    + raceDexterity    + sum(items.dexterity)
    intelligence : Int = baseIntelligence + 2 + levelIntelligence + raceIntelligence + sum(items.intelligence)
    wisdom       : Int = baseWisdom       + 2 + levelWisdom       + raceWisdom       + sum(items.wisdom)
    charisma     : Int = baseCharisma     + 2 + levelCharisma     + raceCharisma     + sum(items.charisma)
    
    maximumHitPoints     : Int = sum(items.maximumHitPoints)     + sum(boons.maximumHitPoints)
    power                : Int = sum(items.power)                + sum(boons.power)
    criticalStrike       : Int = sum(items.criticalStrike)       + sum(boons.criticalStrike)
    armorPenetration     : Int = sum(items.armorPenetration)     + sum(boons.armorPenetration)
    recovery             : Int = sum(items.recovery)             + sum(boons.recovery)
    actionPointGain      : Int = sum(items.actionPointGain)      + sum(boons.actionPointGain)
    combatAdvantageBonus : Int = sum(items.combatAdvantageBonus) + sum(boons.combatAdvantageBonus)
    controlBonus         : Int = sum(items.controlBonus)         + sum(boons.controlBonus)
    defense              : Int = sum(items.defense)              + sum(boons.defense)
    deflect              : Int = sum(items.deflect)              + sum(boons.deflect)
    regeneration         : Int = sum(items.regeneration)         + sum(boons.regeneration)
    lifeSteal            : Int = sum(items.lifeSteal)            + sum(boons.lifeSteal)
    tenacity             : Int = sum(items.tenacity)             + sum(boons.tenacity)
    staminaGain          : Int = sum(items.staminaGain)          + sum(boons.staminaGain)
    incomingHealingBonus : Int = sum(items.incomingHealingBonus) + sum(boons.incomingHealingBonus)
    aoeResist            : Int = sum(items.aoeResist)            + sum(boons.aoeResist)
    controlResist        : Int = sum(items.controlResist)        + sum(boons.controlResist)
    movement             : Int = sum(items.movement)             + sum(boons.movement)
    companionInfluence   : Int = sum(items.companionInfluence)   + sum(boons.companionInfluence)
    goldGain             : Int = sum(items.goldGain)             + sum(boons.goldGain)
    
    armorClass           : Int = sum(items.armorClass)
    totalItemLevel       : Int = sum(items.itemLevel)

    criticalChance                : Float = sum(boons.criticalChance) + ((charisma - 10) as Float) + criticalStrike/400
    criticalSeverity              : Float = sum(boons.criticalSeverity) // ...
    resistanceIgnored             : Float = sum(boons.resistanceIgnored) // ...
    rechargeSpeedIncrease         : Float = sum(boons.rechargeSpeedIncrease) // ...
    actionPointGainStat           : Float = sum(boons.actionPointGainStat) // ...
    damageResistance              : Float = sum(boons.damageResistance) // ...
    deflectionChance              : Float = sum(boons.deflectionChance) // ...
    deflectionSeverity            : Float = sum(boons.deflectionSeverity) // ...
    healthRegeneration            : Float = sum(boons.healthRegeneration) // ...
    bonusIncomingHealing          : Float = sum(boons.bonusIncomingHealing) // ...
    lifeStealChance               : Float = sum(boons.lifeStealChance) // ...
    lifeStealSeverity             : Float = sum(boons.lifeStealSeverity) // ...
    damageResistancePvP           : Float = sum(boons.damageResistancePvP) // ...
    armorPenetrationResistancePvP : Float = sum(boons.armorPenetrationResistancePvP) // ...
    criticalStrikeResistancePvP   : Float = sum(boons.criticalStrikeResistancePvP) // ...
    controlResistancePvP          : Float = sum(boons.controlResistancePvP) // ...
    xpBonus                       : Float = sum(boons.xpBonus) // ...
    goldBonus                     : Float = sum(boons.goldBonus) // ...
    gloryBonus                    : Float = sum(boons.gloryBonus) // ...
    runSpeedBonus                 : Float = sum(boons.runSpeedBonus) // ...
  
  }
  
  relation Character.head      ? <-> 1 Head
  relation Character.armor     ? <-> 1 Armor
  relation Character.arms      ? <-> 1 Arms
  relation Character.mainHand  ? <-> 1 MainHand
  relation Character.offHand   ? <-> 1 OffHand
  relation Character.feet      ? <-> 1 Feet
  relation Character.neck      ? <-> 1 Neck
  relation Character.rightRing ? <-> 1 Ring
  relation Character.leftRing  ? <-> 1 Ring.character2
  relation Character.waist     ? <-> 1 Waist
  relation Character.shirt     ? <-> 1 Shirt
  relation Character.trousers  ? <-> 1 Trousers
  
  relation Character.items * =
    head ++ armor ++ arms ++ mainHand ++ offHand ++ feet ++ neck ++ rightRing ++ leftRing ++ waist ++ shirt ++ trousers
    <-> * ItemInstance
  
  entity Head     extends ItemInstance { }
  entity Armor    extends ItemInstance { }
  entity Arms     extends ItemInstance { }
  trait  MainHand extends ItemInstance { }
  trait  OffHand  extends ItemInstance { }
  entity Feet     extends ItemInstance { }
  entity Neck     extends ItemInstance { }
  entity Ring     extends ItemInstance { }
  entity Waist    extends ItemInstance { }
  entity Shirt    extends ItemInstance { }
  entity Trousers extends ItemInstance { }
  
//  entity AnyHand      extends MainHand, OffHand { } // items that can be equipped on both hands //TODO: diamond inheritance problem
  entity OnlyMainHand extends MainHand { }
  entity OnlyOffHand  extends OffHand { }
  
  trait ItemInstance extends AbilityScores, Ratings, ItemRatings {
    name : String = item.name
    
    rank : Int?
    
    // ability scores
    strength     : Int = item.strength
    constitution : Int = item.constitution
    dexterity    : Int = item.dexterity
    intelligence : Int = item.intelligence
    wisdom       : Int = item.wisdom
    charisma     : Int = item.charisma
    
    // armor class, hit points and total item level
    armorClass           : Int = item.armorClass           + sum(enchantments.armorClass)
    itemLevel            : Int = item.itemLevel            + sum(enchantments.itemLevel)
    maximumHitPoints     : Int = item.maximumHitPoints     + sum(enchantments.maximumHitPoints)
    
    // ratings
    power                : Int = item.power                + sum(enchantments.power)
    criticalStrike       : Int = item.criticalStrike       + sum(enchantments.criticalStrike)
    armorPenetration     : Int = item.armorPenetration     + sum(enchantments.armorPenetration)
    recovery             : Int = item.recovery             + sum(enchantments.recovery)
    actionPointGain      : Int = item.actionPointGain      + sum(enchantments.actionPointGain)
    combatAdvantageBonus : Int = item.combatAdvantageBonus + sum(enchantments.combatAdvantageBonus)
    controlBonus         : Int = item.controlBonus         + sum(enchantments.controlBonus)
    defense              : Int = item.defense              + sum(enchantments.defense)
    deflect              : Int = item.deflect              + sum(enchantments.deflect)
    regeneration         : Int = item.regeneration         + sum(enchantments.regeneration)
    lifeSteal            : Int = item.lifeSteal            + sum(enchantments.lifeSteal)
    tenacity             : Int = item.tenacity             + sum(enchantments.tenacity)
    staminaGain          : Int = item.staminaGain          + sum(enchantments.staminaGain)
    incomingHealingBonus : Int = item.incomingHealingBonus + sum(enchantments.incomingHealingBonus)
    aoeResist            : Int = item.aoeResist            + sum(enchantments.aoeResist)
    controlResist        : Int = item.controlResist        + sum(enchantments.controlResist)
    movement             : Int = item.movement             + sum(enchantments.movement)
    companionInfluence   : Int = item.companionInfluence   + sum(enchantments.companionInfluence)
    goldGain             : Int = item.goldGain             + sum(enchantments.goldGain)
  }
  
  relation ItemInstance.enchantments * <-> ? ItemInstance.slottedIn
  
  relation ItemInstance 1 <-> Item.instances
  
  entity Item extends AbilityScores, Ratings, ItemRatings {
    name : String
  }
  
  relation Character.boons <-> Boon.characters
  
  entity Boon extends Ratings, Stats {
  
  }

  trait AbilityScores {
    strength     : Int = 0 (default)
    constitution : Int = 0 (default)
    dexterity    : Int = 0 (default)
    intelligence : Int = 0 (default)
    wisdom       : Int = 0 (default)
    charisma     : Int = 0 (default)
  }
  
  trait Ratings {
    maximumHitPoints     : Int = 0 (default)
    power                : Int = 0 (default)
    criticalStrike       : Int = 0 (default)
    armorPenetration     : Int = 0 (default)
    recovery             : Int = 0 (default)
    actionPointGain      : Int = 0 (default)
    combatAdvantageBonus : Int = 0 (default)
    controlBonus         : Int = 0 (default)
    defense              : Int = 0 (default)
    deflect              : Int = 0 (default)
    regeneration         : Int = 0 (default)
    lifeSteal            : Int = 0 (default)
    tenacity             : Int = 0 (default)
    staminaGain          : Int = 0 (default)
    incomingHealingBonus : Int = 0 (default)
    aoeResist            : Int = 0 (default)
    controlResist        : Int = 0 (default)
    movement             : Int = 0 (default)
    companionInfluence   : Int = 0 (default)
    goldGain             : Int = 0 (default)
  }
  
  trait ItemRatings{
    armorClass           : Int = 0 (default)
    itemLevel            : Int = 0 (default)
  }
  
  trait Stats {
    criticalChance                : Float = 0.0 (default)
    criticalSeverity              : Float = 0.0 (default)
    resistanceIgnored             : Float = 0.0 (default)
    rechargeSpeedIncrease         : Float = 0.0 (default)
    actionPointGainStat           : Float = 0.0 (default)
    damageResistance              : Float = 0.0 (default)
    deflectionChance              : Float = 0.0 (default)
    deflectionSeverity            : Float = 0.0 (default)
    healthRegeneration            : Float = 0.0 (default)
    bonusIncomingHealing          : Float = 0.0 (default)
    lifeStealChance               : Float = 0.0 (default)
    lifeStealSeverity             : Float = 0.0 (default)
    damageResistancePvP           : Float = 0.0 (default)
    armorPenetrationResistancePvP : Float = 0.0 (default)
    criticalStrikeResistancePvP   : Float = 0.0 (default)
    controlResistancePvP          : Float = 0.0 (default)
    xpBonus                       : Float = 0.0 (default)
    goldBonus                     : Float = 0.0 (default)
    gloryBonus                    : Float = 0.0 (default)
    runSpeedBonus                 : Float = 0.0 (default)
  }