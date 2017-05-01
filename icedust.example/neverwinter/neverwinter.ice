module neverwinter // ctree collection=?+60s constraints=0.25s analysis2=37s // jar collection=?+30s constraints=0.2s analysis2=5s

//model
//
//  entity Character {
//    name : String
//    
//    // ability scores
//    baseStrength     : Int
//    baseConstitution : Int
//    baseDexterity    : Int
//    baseIntelligence : Int
//    baseWisdom       : Int
//    baseCharisma     : Int
//    
//    levelStrength     : Int = 0 (default)
//    levelConstitution : Int = 0 (default)
//    levelDexterity    : Int = 0 (default)
//    levelIntelligence : Int = 0 (default)
//    levelWisdom       : Int = 0 (default)
//    levelCharisma     : Int = 0 (default)
//    
//    raceStrength     : Int = 0 (default)
//    raceConstitution : Int = 0 (default)
//    raceDexterity    : Int = 0 (default)
//    raceIntelligence : Int = 0 (default)
//    raceWisdom       : Int = 0 (default)
//    raceCharisma     : Int = 0 (default)
//    
//    strength     : Int = baseStrength     + 2 + levelStrength     + raceStrength     + sum(items.strength)
//    constitution : Int = baseConstitution + 2 + levelConstitution + raceConstitution + sum(items.constitution)
//    dexterity    : Int = baseDexterity    + 2 + levelDexterity    + raceDexterity    + sum(items.dexterity)
//    intelligence : Int = baseIntelligence + 2 + levelIntelligence + raceIntelligence + sum(items.intelligence)
//    wisdom       : Int = baseWisdom       + 2 + levelWisdom       + raceWisdom       + sum(items.wisdom)
//    charisma     : Int = baseCharisma     + 2 + levelCharisma     + raceCharisma     + sum(items.charisma)
//    
//    // armor class, hit points and total item level
//    armorClass           : Int = sum(items.armorClass)
//    maximumHitPoints     : Int = sum(items.maximumHitPoints)     + sum(boons.maximumHitPoints)
//    totalItemLevel       : Int = sum(items.itemLevel)
//    
//    // ratings
//    power                : Int = sum(items.power)                + sum(boons.power)
//    criticalStrike       : Int = sum(items.criticalStrike)       + sum(boons.criticalStrike)
//    armorPenetration     : Int = sum(items.armorPenetration)     + sum(boons.armorPenetration)
//    recovery             : Int = sum(items.recovery)             + sum(boons.recovery)
//    actionPointGain      : Int = sum(items.actionPointGain)      + sum(boons.actionPointGain)
//    combatAdvantageBonus : Int = sum(items.combatAdvantageBonus) + sum(boons.combatAdvantageBonus)
//    controlBonus         : Int = sum(items.controlBonus)         + sum(boons.controlBonus)
//    defense              : Int = sum(items.defense)              + sum(boons.defense)
//    deflect              : Int = sum(items.deflect)              + sum(boons.deflect)
//    regeneration         : Int = sum(items.regeneration)         + sum(boons.regeneration)
//    lifeSteal            : Int = sum(items.lifeSteal)            + sum(boons.lifeSteal)
//    tenacity             : Int = sum(items.tenacity)             + sum(boons.tenacity)
//    staminaGain          : Int = sum(items.staminaGain)          + sum(boons.staminaGain)
//    incomingHealingBonus : Int = sum(items.incomingHealingBonus) + sum(boons.incomingHealingBonus)
//    aoeResist            : Int = sum(items.aoeResist)            + sum(boons.aoeResist)
//    controlResist        : Int = sum(items.controlResist)        + sum(boons.controlResist)
//    movement             : Int = sum(items.movement)             + sum(boons.movement)
//    companionInfluence   : Int = sum(items.companionInfluence)   + sum(boons.companionInfluence)
//    goldGain             : Int = sum(items.goldGain)             + sum(boons.goldGain)
//    
//    // stats
//  }
//
//  entity Item {
//    name : String
//    
//    // ability scores
//    strength     : Int = 0 (default)
//    constitution : Int = 0 (default)
//    dexterity    : Int = 0 (default)
//    intelligence : Int = 0 (default)
//    wisdom       : Int = 0 (default)
//    charisma     : Int = 0 (default)
//    
//    // armor class, hit points and total item level
//    armorClass           : Int = 0 (default)
//    maximumHitPoints     : Int = 0 (default)
//    itemLevel            : Int
//    
//    // ratings
//    power                : Int = 0 (default)
//    criticalStrike       : Int = 0 (default)
//    armorPenetration     : Int = 0 (default)
//    recovery             : Int = 0 (default)
//    actionPointGain      : Int = 0 (default)
//    combatAdvantageBonus : Int = 0 (default)
//    controlBonus         : Int = 0 (default)
//    defense              : Int = 0 (default)
//    deflect              : Int = 0 (default)
//    regeneration         : Int = 0 (default)
//    lifeSteal            : Int = 0 (default)
//    tenacity             : Int = 0 (default)
//    staminaGain          : Int = 0 (default)
//    incomingHealingBonus : Int = 0 (default)
//    aoeResist            : Int = 0 (default)
//    controlResist        : Int = 0 (default)
//    movement             : Int = 0 (default)
//    companionInfluence   : Int = 0 (default)
//    goldGain             : Int = 0 (default)
//    
//    // stats
//  }
//  
//  entity ItemInstance {
//    name : String = item.name
//    
//    rank : Int?
//    
//    // ability scores
//    strength     : Int = item.strength
//    constitution : Int = item.constitution
//    dexterity    : Int = item.dexterity
//    intelligence : Int = item.intelligence
//    wisdom       : Int = item.wisdom
//    charisma     : Int = item.charisma
//    
//    // armor class, hit points and total item level
//    armorClass           : Int = item.armorClass           + sum(enchantments.armorClass)
//    itemLevel            : Int = item.itemLevel            + sum(enchantments.itemLevel)
//    maximumHitPoints     : Int = item.maximumHitPoints     + sum(enchantments.maximumHitPoints)
//    
//    // ratings
//    power                : Int = item.power                + sum(enchantments.power)
//    criticalStrike       : Int = item.criticalStrike       + sum(enchantments.criticalStrike)
//    armorPenetration     : Int = item.armorPenetration     + sum(enchantments.armorPenetration)
//    recovery             : Int = item.recovery             + sum(enchantments.recovery)
//    actionPointGain      : Int = item.actionPointGain      + sum(enchantments.actionPointGain)
//    combatAdvantageBonus : Int = item.combatAdvantageBonus + sum(enchantments.combatAdvantageBonus)
//    controlBonus         : Int = item.controlBonus         + sum(enchantments.controlBonus)
//    defense              : Int = item.defense              + sum(enchantments.defense)
//    deflect              : Int = item.deflect              + sum(enchantments.deflect)
//    regeneration         : Int = item.regeneration         + sum(enchantments.regeneration)
//    lifeSteal            : Int = item.lifeSteal            + sum(enchantments.lifeSteal)
//    tenacity             : Int = item.tenacity             + sum(enchantments.tenacity)
//    staminaGain          : Int = item.staminaGain          + sum(enchantments.staminaGain)
//    incomingHealingBonus : Int = item.incomingHealingBonus + sum(enchantments.incomingHealingBonus)
//    aoeResist            : Int = item.aoeResist            + sum(enchantments.aoeResist)
//    controlResist        : Int = item.controlResist        + sum(enchantments.controlResist)
//    movement             : Int = item.movement             + sum(enchantments.movement)
//    companionInfluence   : Int = item.companionInfluence   + sum(enchantments.companionInfluence)
//    goldGain             : Int = item.goldGain             + sum(enchantments.goldGain)
//    
//    // stats
//  }
//  relation ItemInstance.item 1 <-> * Item.instances
//  relation ItemInstance.enchantments * <-> * ItemInstance.enchants
//  
//  relation Character.items * <-> ? ItemInstance.character
//
//  entity Boon {
////    name : String
//    
//    // hit points
//    maximumHitPoints     : Int = 0 (default)
//    
//    // ratings
//    power                : Int = 0 (default)
//    criticalStrike       : Int = 0 (default)
//    armorPenetration     : Int = 0 (default)
//    recovery             : Int = 0 (default)
//    actionPointGain      : Int = 0 (default)
//    combatAdvantageBonus : Int = 0 (default)
//    controlBonus         : Int = 0 (default)
//    defense              : Int = 0 (default)
//    deflect              : Int = 0 (default)
//    regeneration         : Int = 0 (default)
//    lifeSteal            : Int = 0 (default)
//    tenacity             : Int = 0 (default)
//    staminaGain          : Int = 0 (default)
//    incomingHealingBonus : Int = 0 (default)
//    aoeResist            : Int = 0 (default)
//    controlResist        : Int = 0 (default)
//    movement             : Int = 0 (default)
//    companionInfluence   : Int = 0 (default)
//    goldGain             : Int = 0 (default)
//    
//    // stats
//    criticalChance                : Float = 0.0 (default)
//    criticalSeverity              : Float = 0.0 (default)
//    resistanceIgnored             : Float = 0.0 (default)
//    rechargeSpeedIncrease         : Float = 0.0 (default)
//    actionPointGainStat           : Float = 0.0 (default)
//    damageResistance              : Float = 0.0 (default)
//    deflectionChance              : Float = 0.0 (default)
//    deflectionSeverity            : Float = 0.0 (default)
//    healthRegeneration            : Float = 0.0 (default)
//    bonusIncomingHealing          : Float = 0.0 (default)
//    lifeStealChance               : Float = 0.0 (default)
//    lifeStealSeverity             : Float = 0.0 (default)
//    damageResistancePvP           : Float = 0.0 (default)
//    armorPenetrationResistancePvP : Float = 0.0 (default)
//    criticalStrikeResistancePvP   : Float = 0.0 (default)
//    controlResistancePvP          : Float = 0.0 (default)
//    xpBonus                       : Float = 0.0 (default)
//    goldBonus                     : Float = 0.0 (default)
//    gloryBonus                    : Float = 0.0 (default)
//    runSpeedBonus                 : Float = 0.0 (default)
//  }
//
//  relation Character.boons * <-> * Boon.characters
//
//data
//
//  // game data
//  elementalDragonflightAssaultCap : Item {
//    name = "Elemental Dragonflight Assault Cap"
//    itemLevel = 142
//    maximumHitPoints = 10968
//    criticalStrike = 974
//    armorPenetration = 649
//    defense = 351
//  }
//  elementalDragonflightRaidRobes : Item {
//    name = "Elemental Dragonflight Raid Robes"
//    itemLevel = 142
//    armorClass = 7
//    maximumHitPoints = 21937
//    power = 1010
//    recovery = 1515
//    defense = 526
//  }
//  elementalDragonflightRaidArmlets : Item {
//    name = "Elemental Dragonflight Raid Armlets"
//    itemLevel = 142
//    maximumHitPoints = 10968
//    power = 649
//    criticalStrike = 974
//    defense = 351
//  }
//  elementalDragonflightRaidShoes : Item {
//    name = "Elemental Dragonflight Raid Shoes"
//    itemLevel = 142
//    maximumHitPoints = 10968
//    power = 649
//    recovery = 974
//    defense = 351
//  }
//  
//  twistedSkulls : Item {
//    name = "Twisted Skulls"
//    itemLevel = 144 // gives 4 more than the listed 140
//    power = 5041
//    criticalStrike = 968
//    recovery = 968
//  }
//  twistedTalisman : Item {
//    name = "Twisted Talisman"
//    itemLevel = 148 // gives 8 more than the listed 140
//    power = 1306
//    criticalStrike = 774
//    recovery = 774
//  }
//  lostmauthsHoardNecklace : Item {
//    name = "Lostmauth's Hoard Necklace"
//    itemLevel = 135
//    power = 846
//    criticalStrike = 530
//    armorPenetration = 530
//  }
//  goldenBeltOfPuissance : Item {
//    name = "Golden Belt of Puissance"
//    itemLevel = 135
//    strength = 2
//    dexterity = 2
//    power = 846
//    criticalStrike = 530
//    armorPenetration = 530
//  }
//  
//  personalizedAdamantRingofPiercing : Item {
//    name = "Personalized Adamant Ring of Piercing"
//    itemLevel = 135
//    power = 394
//    armorPenetration = 394
//  }
//  personalizedAdamantRingofRecovery : Item {
//    name = "Personalized Adamant Ring of Recovery"
//    itemLevel = 135
//    power = 394
//    recovery = 394
//  }
//  
//  gemmedExquisiteElementalShirt : Item {
//    name = "Gemmed Exquisite Elemental Shirt"
//    itemLevel = 145
//    power = 228
//    criticalStrike = 228
//    armorPenetration = 114
//    defense = 90
//  }
//  gemmedExquisiteElementalPants : Item {
//    name = "Gemmed Exquisite Elemental Pants"
//    itemLevel = 145
//    power = 228
//    recovery = 114
//    armorPenetration = 228
//    defense = 93
//  }
//  
//  sigilOfTheDevoted : Item {
//    name = "Sigil of the Devoted"
//    itemLevel = 160
//    power = 1000
//    defense = 1000
//    incomingHealingBonus = 600
//  }
//  sigilOfTheGreatWeapon : Item {
//    name = "Sigil of the Great Weapon"
//    itemLevel = 160
//    maximumHitPoints = 2400
//    power = 1000
//    armorPenetration = 1000
//  }
//  vanguardsBanner : Item {
//    name = "Vanguard's Banner"
//    itemLevel = 160
//    maximumHitPoints = 4000
//    power = 1000
//    lifeSteal = 600
//  }
//  lostmauthsHornOfBlasting : Item {
//    name = "Lostmauth's Horn of Blasting"
//    itemLevel = 160
//    power = 1000
//    armorPenetration = 1000
//    controlBonus = 600
//  }
//  
//  savageEnchantmentRank12Defense : Item {
//    name = "Savage Enchantment, Rank 12"
//    itemLevel = 82
//    maximumHitPoints = 1680
//    lifeSteal = 420
//  }
//  brutalEnchantmentRank12Offense : Item {
//    name = "Brutal Enchantment, Rank 12"
//    itemLevel = 82
//    power = 420
//    criticalStrike = 420
//  }
//  dragonsHoardEnchantment : Item {
//    name = "Dragons's Hoard Enchantment"
//    itemLevel = 48
//  }
//  greaterDragonsHoardEnchantment : Item {
//    name = "Greater Dragons's Hoard Enchantment"
//    itemLevel = 58
//  }
//  
//  lesserSoulforgedEnchantment : Item {
//    name = "Lesser Soulforged Enchantment"
//    itemLevel = 32
//  }
//  perfectVorpalEnchantment : Item {
//    name = "Perfect Vorpal Enchantment"
//    itemLevel = 58
//  }
//  
//  majorCriticalStrikeArmorKit : Item {
//    name = "Major Critical Strike Armor Kit"
//    itemLevel = 35
//    criticalStrike = 200
//  }
//  
//  majorActionPointGainJewel : Item {
//    name = "Major Action Point Gain Jewel"
//    itemLevel = 35
//    actionPointGain = 100
//  }
//  
//  darkFeyWarden            : Boon { defense = 400 }
//  darkFeyHunter            : Boon { power = 400 }
//  feyElusiveness           : Boon { deflect = 400 }
//  feyPrecision             : Boon { criticalStrike = 400 }
//  feywildsFirtitude        : Boon { maximumHitPoints = 1600 }
//  elvenHaste               : Boon { actionPointGainStat = 0.03 }
//  elvenTranquility         : Boon {}
//  elvenFerocity            : Boon {}
//  elvenResolve             : Boon {}
//  feyThistle               : Boon {}
//  elvishFury               : Boon {}
//  redcapBrew               : Boon {}
//  
//  reliquaryKeepersStrength : Boon { power = 250 movement = 250 }
//  conjurersGambit          : Boon { criticalStrike = 250 movement = 250 }
//  evokersThirst            : Boon { lifeSteal = 400 }
//  illusoryRegeneration     : Boon { regeneration = 400 }
//  illusionShimmer          : Boon { deflectionChance = 0.03 }
//  forbiddenPiercing        : Boon { resistanceIgnored = 0.03 }
//  enragedRegrowth          : Boon {}
//  shadowtouch              : Boon {} 
//  augmentedThayanBastion   : Boon {}
//  rampagingMadness         : Boon {}
//  endlessConsumption       : Boon {}
//  burningGuidance          : Boon {}
//  
//  weatheringTheStorm       : Boon { aoeResist = 400 }
//  encroachingTactics       : Boon { combatAdvantageBonus = 400 }
//  appreciationOfWarmth     : Boon { incomingHealingBonus = 400 }
//  refreshingChill          : Boon { staminaGain = 400 }
//  rapidThaw                : Boon { recovery = 400 }
//  sleetSkills              : Boon { criticalSeverity = 0.02 }
//  coldShoulder             : Boon {}
//  coolResolve              : Boon {}
//  avalanche                : Boon {}
//  tousingWarmth            : Boon {}
//  wintersBounty            : Boon {}
//  sharedSurvival           : Boon {}
//  
//  dragonheart              : Boon { maximumHitPoints = 1600 }
//  dragonsClaws             : Boon { power = 400 }
//  dragonsShadow            : Boon { deflect = 400 }
//  dragonsGaze              : Boon { criticalStrike = 400 }
//  dragonsDefense           : Boon { defense = 400 }
//  draconicArmorbreaker     : Boon { armorPenetration = 400 }
//  dragonsGreed             : Boon { lifeSteal = 400 }
//  dragonsBlood             : Boon { regeneration = 400 }
//  dragonsThirst            : Boon { lifeStealChance = 0.04 }      // rank 1, advertised as 3% but gives 4%
//  dragonsRevival           : Boon { bonusIncomingHealing = 0.10 } // rank 1
//  dragonsFury              : Boon { criticalSeverity = 0.05 }     // rank 1
//  dragonsGrip              : Boon {}                              // rank 1, "Grants 10% increased Control Strength." -> stat?
//
//  primordialVitality       : Boon { defense = 400 maximumHitPoints = 1600 }
//  primordialMight          : Boon { power = 400 maximumHitPoints = 1600 }
//  primordialRegenesis      : Boon { lifeSteal = 400 maximumHitPoints = 1600 }
//  primordialFocus          : Boon { criticalStrike = 400 maximumHitPoints = 1600 }
//  drowMeditation           : Boon { regeneration = 1200 }
//  drowAmbushTactics        : Boon {} // "Combat Advantage damage bonus is increased by 10%." -> stat?
//  dwarvenFooting           : Boon {} // "Control Effects will now have a 5% shorter duration when applied to you." -> stat?
//  dwarvenStamina           : Boon {} // "You now regain Stamina 5% faster." -> stat?
//  demonicDomination        : Boon {}
//  abyssalTenacity          : Boon {}
//  demonSlayer              : Boon {}
//  abyssalStrikes           : Boon {}
//
//  guildArmorPenetrationRank8 : Boon { armorPenetration = 6000 }
//  guildLifeStealRank8        : Boon { lifeSteal = 6400 }
//
//  // characters
//  controlWizard : Character {
//    name = "My Wizard"
//    baseStrength = 10
//    baseConstitution = 10
//    baseDexterity = 8
//    baseIntelligence = 18
//    baseWisdom = 13
//    baseCharisma = 13
//    raceIntelligence = 2
//    raceCharisma = 2
//    levelIntelligence = 5
//    levelCharisma = 5
//    boons =
//      darkFeyHunter,
//      feyPrecision,
//      feywildsFirtitude,
//      elvenFerocity,
//      elvenResolve,
//      reliquaryKeepersStrength,
//      evokersThirst,
//      illusionShimmer,
//      shadowtouch,
//      endlessConsumption,
//      encroachingTactics,
//      refreshingChill,
//      sleetSkills,
//      coolResolve,
//      wintersBounty,
//      dragonheart,
//      dragonsGaze,
//      dragonsDefense,
//      dragonsGreed,
//      dragonsThirst,
//      dragonsFury,
//      primordialMight,
//      primordialRegenesis,
//      drowAmbushTactics,
//      dwarvenStamina,
//      guildArmorPenetrationRank8,
//      guildLifeStealRank8
//    items =
//      helm {
//        item = elementalDragonflightAssaultCap
//        enchantments =
//          {
//            item = greaterDragonsHoardEnchantment
//          },
//          {
//            item = majorCriticalStrikeArmorKit
//          },
//          {
//            item = {
//              name = "Dragon Flight Set Bonus"
//              itemLevel = 0
//              maximumHitPoints = 2000
//              power = 500
//            }
//          }
//      },
//      chest {
//        item = elementalDragonflightRaidRobes
//        enchantments =
//          {
//            item = savageEnchantmentRank12Defense
//            rank = 12
//          },
//          {
//            item = lesserSoulforgedEnchantment
//          },
//          {
//            item = majorCriticalStrikeArmorKit
//          }
//      },
//      arms {
//        item = elementalDragonflightRaidArmlets
//        enchantments =
//          {
//            item = greaterDragonsHoardEnchantment
//          },
//          {
//            item = majorCriticalStrikeArmorKit
//          }
//      },
//      mainHand {
//        item = twistedSkulls
//        rank = 60
//        enchantments =
//          {
//            item = brutalEnchantmentRank12Offense
//            rank = 12
//          },
//          {
//            item = brutalEnchantmentRank12Offense
//            rank = 12
//          },
//          {
//            item = perfectVorpalEnchantment
//          },
//          {
//            item = {
//              name = "Twisted Set Bonus"
//              itemLevel = 0
//              power = 2080   // initial 13 offensive stacks of 160
//              defense = 1920 // initial 12 defenseive stacks of 160
//            }
//          }
//      },
//      offHand {
//        item = twistedTalisman
//        rank = 60
//        enchantments =
//          {
//            item = brutalEnchantmentRank12Offense
//            rank = 12
//          },
//          {
//            item = savageEnchantmentRank12Defense
//            rank = 12
//          },
//          {
//            item = {
//              name = "Artifact Stat Increase"
//              itemLevel = 0
//              combatAdvantageBonus = 366
//            }
//          }
//      },
//      boots {
//        item = elementalDragonflightRaidShoes
//        enchantments =
//          {
//            item = dragonsHoardEnchantment
//          },
//          {
//            item = majorCriticalStrikeArmorKit
//          }
//      },
//      neck {
//        item = lostmauthsHoardNecklace
//        rank = 60
//        enchantments =
//          {
//            item = dragonsHoardEnchantment
//          },
//          {
//            item = brutalEnchantmentRank12Offense
//            rank = 12
//          },
//          {
//            item = majorActionPointGainJewel
//          }
//      },
//      ring1 {
//        item = personalizedAdamantRingofPiercing
//        enchantments =
//          {
//            item = brutalEnchantmentRank12Offense
//            rank = 12
//          },
//          {
//            item = savageEnchantmentRank12Defense
//            rank = 12
//          },
//          {
//            item = majorActionPointGainJewel
//          }
//      },
//      ring2 {
//        item = personalizedAdamantRingofRecovery
//        enchantments =
//          {
//            item = brutalEnchantmentRank12Offense
//            rank = 12
//          },
//          {
//            item = savageEnchantmentRank12Defense
//            rank = 12
//          },
//          {
//            item = majorActionPointGainJewel
//          }
//      },
//      waist {
//        item = goldenBeltOfPuissance
//        rank = 60
//        enchantments =
//          {
//            item = dragonsHoardEnchantment
//          },
//          {
//            item = savageEnchantmentRank12Defense
//            rank = 12
//          },
//          {
//            item = majorActionPointGainJewel
//          }
//      },
//      shirt {
//        item = gemmedExquisiteElementalShirt
//        enchantments =
//          {
//            item = brutalEnchantmentRank12Offense
//            rank = 12
//          }
//      },
//      trousers {
//        item = gemmedExquisiteElementalPants
//        enchantments =
//          {
//            item = savageEnchantmentRank12Defense
//            rank = 12
//          }
//      },
//      artifact1 {
//        item = sigilOfTheDevoted
//      },
//      artifact2 {
//        item = sigilOfTheGreatWeapon
//      },
//      artifact3 {
//        item = vanguardsBanner
//      },
//      artifact4 {
//        item = lostmauthsHornOfBlasting
//      }
//      
//  }
//  
//execute
//
//  controlWizard.name
//  "Strength:               " + controlWizard.strength             as String
//  "Constitution:           " + controlWizard.constitution         as String
//  "Dexterity:              " + controlWizard.dexterity            as String
//  "Intelligence:           " + controlWizard.intelligence         as String
//  "Wisdom:                 " + controlWizard.wisdom               as String
//  "Charisma:               " + controlWizard.charisma             as String
//  "Amor Class:             " + controlWizard.armorClass           as String
//  "Maximum Hit Points:     " + controlWizard.maximumHitPoints     as String
//  "Total Item Level:       " + controlWizard.totalItemLevel       as String
//  "Power:                  " + controlWizard.power                as String
//  "Critical Strike:        " + controlWizard.criticalStrike       as String
//  "Armor Penetration:      " + controlWizard.armorPenetration     as String
//  "Recovery:               " + controlWizard.recovery             as String
//  "Action Point Gain:      " + controlWizard.actionPointGain      as String
//  "Combat Advantage Bonus: " + controlWizard.combatAdvantageBonus as String
//  "Control Bonus:          " + controlWizard.controlBonus         as String
//  "Defense:                " + controlWizard.defense              as String
//  "Deflect:                " + controlWizard.deflect              as String
//  "Regeneration:           " + controlWizard.regeneration         as String
//  "Life Steal:             " + controlWizard.lifeSteal            as String
//  "Tenacity (PVP):         " + controlWizard.tenacity             as String
//  "Stamina Gain:           " + controlWizard.staminaGain          as String
//  "Incoming Healing Bonus: " + controlWizard.incomingHealingBonus as String
//  "AoE Resist:             " + controlWizard.aoeResist            as String
//  "Control Resist:         " + controlWizard.controlResist        as String
//  "Movement:               " + controlWizard.movement             as String
//  "Companion Influence:    " + controlWizard.companionInfluence   as String
//  "Gold Gain:              " + controlWizard.goldGain             as String
