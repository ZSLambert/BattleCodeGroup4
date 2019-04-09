import battlecode as bc
import random
import sys
import traceback
import time
import math
import numpy as np

import os

print(os.getcwd())

print("pystarting")

# A GameController is the main type that you talk to the game with.
# Its constructor will connect to a running game.
gc = bc.GameController()
directions = list(bc.Direction)

totalBFSTime = 0
totalNearbyKarbTime = 0
unreachableTime = 0
avoidanceTime = 0
successCount = 0
healCount = 0


class Memory:
    worker_paths = {}
    reachable_clusters = []
    combat_paths = {}
    combat_destinations = {}
    current_vision_earth = {}
    current_vision_mars = {}
    finishedKarb = False
    marsTroop_paths = {}
    rocket_destination = {}
    marsTroops = []
    worker_turns_stuck = {}


class Constants:
    LAUNCH_BY = 749
    DESIRED_WORKERS = 10
    DESIRED_FACTORIES = 4
    HEALER_MAX_WEIGHT = 25
    DESIRED_ROCKETS = 4
    DIRECTION_CHANGES = [(0, 1), (0, -1), (1, 0), (-1, 0), (1, 1), (-1, -1), (1, -1), (-1, 1)]
    REPLICATE_COST = 60
    WORKER_COST = 50
    OTHER_COST = 40
    ROCKET_COST = 150
    FACTORY_COST = 200
    HARVEST_AMOUNT = 3
    CHANGE_FROM_DIRECT = {
        bc.Direction.Center: (0, 0),
        bc.Direction.South: (0, -1),
        bc.Direction.North: (0, 1),
        bc.Direction.East: (1, 0),
        bc.Direction.West: (-1, 0),
        bc.Direction.Southeast: (1, -1),
        bc.Direction.Southwest: (-1, -1),
        bc.Direction.Northeast: (1, 1),
        bc.Direction.Northwest: (-1, 1)
    }
    DESTINATION_REACHED = [(-1000, -1000)]
    RANGER_VISION = 70
    WKH_VISION = 50
    MAGE_VISION = 30
    ROCKET_VISION = 2
    HEALER_VISION = 50
    HEALER_RANGE = 30
    RANGER_RANGE = 50
    MAGE_RANGE = 30
    KNIGHT_RANGE = 2
    INITIAL_KARB_COUNT = 0
    START_POINTS = []
    ENEMY_START_POINTS = []
    DANGEROUS_ENEMIES = [bc.UnitType.Ranger, bc.UnitType.Mage, bc.UnitType.Knight]
    ENEMIES_UNREACHABLE = False


class MyVars:
    workerCount = 0
    rangerCount = 0
    rocketCount = 0
    factoryCount = 0
    knightCount = 0
    mageCount = 0
    healerCount = 0
    
    #used for ranger,mage and healer production, more weight means more will be produced
    rangerWeight = 10
    mageWeight = 10
    healerWeight = 0

    marsWorkerCount = 0
    marsRangerCount = 0
    marsMageCount = 0
    marsHealerCount = 0

    #stores factory and rocket locations
    factoryLocations = []
    rocketLocations = []


print("pystarted")

# It's a good idea to try to keep your bots deterministic, to make debugging easier.
# determinism isn't required, but it means that the same things will happen in every thing you run,
# aside from turns taking slightly different amounts of time due to noise.
random.seed(6137)

my_team = gc.team()


#used to invert a direction to the opposite of what it is
def invertDirection(direction):
    if direction == bc.Direction.North:
        return bc.Direction.South
    if direction == bc.Direction.South:
        return bc.Direction.North
    if direction == bc.Direction.East:
        return bc.Direction.West
    if direction == bc.Direction.West:
        return bc.Direction.East
    if direction == bc.Direction.Northeast:
        return bc.Direction.Southwest
    if direction == bc.Direction.Northwest:
        return bc.Direction.Southeast
    if direction == bc.Direction.Southeast:
        return bc.Direction.Northwest
    if direction == bc.Direction.Southwest:
        return bc.Direction.Northeast
    return bc.Direction.Center


# inverts a point on the map - used to estimate where the enemy will be
def invertPoint(point, planet):
    ptX = point[0]
    ptY = point[1]
    different_inversions = []

    different_inversions.append((earthMap.width - ptX - 1, earthMap.height - ptY - 1))
    different_inversions.append((ptX, earthMap.height - ptY - 1))
    different_inversions.append((earthMap.width - ptX - 1, ptY))

    return different_inversions


# determines whether a map location is on the map based on its x and y coordinates
def onMap(loc):
    x = loc.x
    y = loc.y
    if loc.planet == bc.Planet.Earth:
        if x < 0 or x >= earthWidth or y < 0 or y >= earthHeight:
            return False
    elif loc.planet == bc.Planet.Mars:
        if x < 0 or x >= marsWidth or y < 0 or y >= marsHeight:
            return False
    return True


# takes in a list of locations and finds the one "closest" to the destination based on a simple
# distance heuristic.  It also returns the index of the location it chose.
def lowestDist(locList, destination):
    lowest = 1000000
    choice = locList[0]
    index = 0
    for i in range(len(locList)):
        distance = pow(destination.x - locList[i][0], 2) + pow(destination.y - locList[i][1], 2)
        if distance < lowest:
            lowest = distance
            choice = locList[i]
            index = i
    return choice, index

#evaluates a spot to build a potential factory or rocket at - penalties are given to spots on 
#karbonite, or spots that border unpassable terrain - this attempts to make it so structures
#are not built that completely block off one side of the map
def evalFactorySpot(location):
    score = 100

    if (location.x, location.y) in karboniteMapEarth:
        score -= 100

    for change in Constants.DIRECTION_CHANGES:
        newLoc = bc.MapLocation(location.planet, location.x + change[0], location.y + change[1])
        if onMap(newLoc):
            if not earthMap.is_passable_terrain_at(newLoc) or newLoc in MyVars.factoryLocations:
                score -= 30
        else:
            score -= 30
    return score


# takes in a unit and a maplocation of a destination, then will return whatever step needs to be taken
# to reach the destination quickest
# current pathfinding algorithm
def BFS_firstStep(unit, destination):
    global totalBFSTime
    global unreachableTime
    # get the position of the unit that we are trying to move.

    startT = int(round(time.time() * 1000))

    start = unit.location.map_location()

    startLoc = (start.x, start.y)
    destLoc = (destination.x, destination.y)


    planet = start.planet

    parent = {}
    queue = [startLoc]
    visited = []
    while queue:
        # to intelligently choose nodes, get the one with the lowest straight line distance to destination, then remove that node from the queue.
        node, index = lowestDist(queue, destination)
        queue.pop(index)
        visited.append(node)
        if node == destLoc:
            # starts a list which will track the entire path from the end to the exit
            # ends up reversing it and returning the location of the first step
            path = [destLoc]
            while path[-1] != startLoc:
                path.append(parent[path[-1]])
            path.reverse()
            totalBFSTime += int(round(time.time() * 1000)) - startT
            # debugging in case we ever have the same destination as start point
            if len(path) == 1:
                return Constants.DESTINATION_REACHED
            return path[1:]

        neighbors = getNeighbors(bc.MapLocation(planet, node[0], node[1]))

        for adjacent in getNeighbors(bc.MapLocation(planet, node[0], node[1])):
            taken = False
            try:
                if not gc.is_occupiable(adjacent):
                    thatUnit = gc.sense_nearby_units(adjacent, 1)
                    if thatUnit.unit_type == bc.UnitType.Factory or thatUnit.unit_type == bc.UnitType.Rocket:
                        taken = True
            except:
                taken = False
            adjLoc = (adjacent.x, adjacent.y)

            if not taken and adjLoc not in visited and adjLoc not in queue:
                parent[adjLoc] = node  # <<<<< record the parent of the node - used to get the path
                queue.append(adjLoc)
    # handles cases where we are trying to reach an unreachable destination.
    unreachableTime += int(round(time.time() * 1000)) - startT
    return Constants.DESTINATION_REACHED

#from a starting location, maps out all the spots that can be reached from it
def getReachable(unit):
    start = unit.location.map_location()

    planet = start.planet

    startLoc = (start.x, start.y)
    queue = []
    visited = []
    queue.append(startLoc)
    while queue:
        node = queue.pop(0)
        visited.append(node)
        for adjacent in getNeighbors(bc.MapLocation(planet, node[0], node[1])):
            adjLoc = (adjacent.x, adjacent.y)
            if adjLoc not in visited and adjLoc not in queue:
                queue.append(adjLoc)
    return visited

#maps reachable spots into different clusters - useful for maps where two units start on two "islands"
#this makes it so that people on one cluster dont try to pathfind their way to an unreachable cluster,
#which is impossible
def mapReachable():
    for unit in gc.my_units():
        # make a coordinate from the location
        loc = unit.location.map_location().x, unit.location.map_location().y
        alreadySearched = False
        for cluster in Memory.reachable_clusters:
            if loc in cluster:
                placeholder = alreadySearched = True
        if not alreadySearched:
            newCluster = getReachable(unit)
            Memory.reachable_clusters.append(newCluster)

#given a map location, generates all the neighbors of this location that are passable terrain
def getNeighbors(location):
    neighbors = []
    # goes through all the different changes that could be applied to a position, and adds them to our list if they have passable terrain
    for change in Constants.DIRECTION_CHANGES:
        tempLoc = bc.MapLocation(location.planet, location.x + change[0], location.y + change[1])
        if onMap(tempLoc):
            if location.planet == bc.Planet.Earth:
                if earthMap.is_passable_terrain_at(tempLoc):
                    neighbors.append(tempLoc)
            elif location.planet == bc.Planet.Mars:
                if marsMap.is_passable_terrain_at(tempLoc):
                    neighbors.append(tempLoc)

    return neighbors


# find the closest location - based on simple heuristic - with karbonite to our initial location.
def nearbyKarb(location, planet):
    global totalNearbyKarbTime
    startT = int(round(time.time() * 1000))

    #check to make sure theres no karbonite right near us - no points in going through everything if there is.  makes it so that maps like Julia dont take forever to run nearbyKarb
    toCheck = getNeighbors(location)
    toCheck.append(location)
    for spot in toCheck:
        tup = (spot.x, spot.y)
        if tup in karboniteMapEarth:
            totalNearbyKarbTime += int(round(time.time() * 1000)) - startT
            return spot
    
    #lists all the destinations that other workers are currently going to
    takenDest = []
    for key in Memory.worker_paths:
        try:
            takenDest.append(Memory.worker_paths[key][-1])
        except:
            placeHolder = True

    locCluster = []
    for cluster in Memory.reachable_clusters:
        if (location.x, location.y) in cluster:
            locCluster = cluster
    minDist = 100000
    minDistLoc = location
    if planet == bc.Planet.Earth:
        for key in karboniteMapEarth:
            if key in takenDest or key not in locCluster:
                # we dont want to send two workers to the exact same place
                # we also dont want to bother returning a spot thats not reachable
                continue
            tempDist = pow(location.x - key[0], 2) + pow(location.y - key[1], 2)
            if tempDist < minDist:
                minDist = tempDist
                minDistLoc = bc.MapLocation(location.planet, key[0], key[1])
    else:
        for key in karboniteMapMars:
            if key in takenDest or key not in locCluster:
                # we dont want to send two workers to the exact same place
                # we also dont want to bother returning a spot thats not reachable
                continue
            tempDist = pow(location.x - key[0], 2) + pow(location.y - key[1], 2)
            if tempDist < minDist:
                minDist = tempDist
                minDistLoc = bc.MapLocation(location.planet, key[0], key[1])

    totalNearbyKarbTime += int(round(time.time() * 1000)) - startT
    return minDistLoc


# given a unit and a direction, returns the location of the unit moved in that direction.
def locFromDirect(unit, direction):
    location = unit.location.map_location()
    change = Constants.CHANGE_FROM_DIRECT[direction]
    return bc.MapLocation(location.planet, location.x + change[0], location.y + change[1])

#the counterpart to moving units on earth - this is used for mars
def moveMarsUnit(unit):
    curPlanet = unit.location.map_location().planet

    destination = bc.MapLocation(curPlanet, Memory.rocket_destination[unit.id].x,
                                 Memory.rocket_destination[unit.id].y)

    try:

        if not gc.is_occupiable(destination) or not earthMap.is_passable_terrain_at(destination):
            return
    except:
        placeholder = True


    try:
        # get the destination that this unit is supposed to be going to
        path = Memory.marsTroop_paths[unit.id]
        # if we already reached that destination: get a new one
        if path == Constants.DESTINATION_REACHED:
            for i in np.random.permutation(8):
                myDirection = directions[i]
                if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return
    except:
        # this will only happen the first time a destination is generated for a spot
        path = BFS_firstStep(unit, destination)

        Memory.marsTroop_paths[unit.id] = path

    # move in the correct direction to get to our destination if possible.
    try:
        nextStep = bc.MapLocation(unit.location.map_location().planet, path[0][0], path[0][1])

        myDirection = unit.location.map_location().direction_to(nextStep)

        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            # remove the first step of the path that we had.
            Memory.marsTroop_paths[unit.id] = path[1:]
            if (Memory.marsTroop_paths[unit.id] == []):
                Memory.marsTroop_paths[unit.id] = Constants.DESTINATION_REACHED
            return
        else:
            if not gc.is_move_ready(unit.id):
                placeHolder = True
            else:
                for i in np.random.permutation(8):
                    myDirection = directions[i]
                    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                        gc.move_robot(unit.id, myDirection)
                        return
    except:
        for i in np.random.permutation(8):
            myDirection = directions[i]
            if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                gc.move_robot(unit.id, myDirection)
                return

#moves a combat unit towards its destination, which is done differently than moving workers.
def moveCombatUnit(unit):
    curPlanet = unit.location.map_location().planet

    destination = bc.MapLocation(curPlanet, Memory.combat_destinations[unit.id][0],
                                 Memory.combat_destinations[unit.id][1])
    try:

        if not earthMap.is_passable_terrain_at(destination):
            return
    except:
        placeholder = True

    try:
        # get the destination that this unit is supposed to be going to
        path = Memory.combat_paths[unit.id]
        # if we already reached that destination: get a new one
        if path == Constants.DESTINATION_REACHED:
        #if it reached its initial destination, use random movement
                for i in np.random.permutation(8):
                    myDirection = directions[i]
                    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                        gc.move_robot(unit.id, myDirection)
                        return

    except:
        # this will only happen the first time a destination is generated for a spot
        path = BFS_firstStep(unit, destination)

        # they only travel half way to the enemy start point.  Makes it so they don't blindly
        #run into the enemy base one by one
        n = math.floor(len(path) / 2)
        del path[-n:]

        Memory.combat_paths[unit.id] = path

    # move in the correct direction to get to our destination if possible.
    try:
        nextStep = bc.MapLocation(unit.location.map_location().planet, path[0][0], path[0][1])

        myDirection = unit.location.map_location().direction_to(nextStep)
        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            # remove the first step of the path that we had.
            Memory.combat_paths[unit.id] = path[1:]
            if (Memory.combat_paths[unit.id] == []):
                Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED
            return
        else:
            if not gc.is_move_ready(unit.id):
                placeholder = True
            else:
                for i in np.random.permutation(8):
                    myDirection = directions[i]
                    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                        gc.move_robot(unit.id, myDirection)
                        return
    except:
        #if there was an error trying to do this, move in a random direction
        for i in np.random.permutation(8):
            myDirection = directions[i]
            if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                gc.move_robot(unit.id, myDirection)
                return

#moves a worker to its predetermined path.  Only tries to generate more paths if we have a significant
#amount of time left, since sometimes that can be very costly
def moveWorker(unit):
    
    #workers often get stuck trying to head to karbonite when factories are built in their way
    #this piece of code makes it so that if theyve been stuck for 5+ turns, they move randomly
    #and calculate a new destination
    if unit.id in Memory.worker_turns_stuck:
        if Memory.worker_turns_stuck[unit.id] > 5:
            Memory.worker_paths[unit.id] = Constants.DESTINATION_REACHED
            for i in np.random.permutation(8):
                myDirection = directions[i]
                if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return
    
    try:
        # get the destination that this unit is supposed to be going to
        path = Memory.worker_paths[unit.id]
        # if we already reached that destination: get a new one
        if path == Constants.DESTINATION_REACHED:
            if gc.get_time_left_ms() > 3000:
                destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)
                path = BFS_firstStep(unit, destination)
                Memory.worker_paths[unit.id] = path
    except:
        # this will only happen the first time a destination is generated for a spot
        if gc.get_time_left_ms() > 3000:

            destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)

            path = BFS_firstStep(unit, destination)

            Memory.worker_paths[unit.id] = path

    # move in the correct direction to get to our destination if possible.
    try:
        nextStep = bc.MapLocation(unit.location.map_location().planet, path[0][0], path[0][1])

        myDirection = unit.location.map_location().direction_to(nextStep)

        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            Memory.worker_turns_stuck[unit.id] = 0
            # remove the first step of the path that we had.

            Memory.worker_paths[unit.id] = path[1:]
            if (Memory.worker_paths[unit.id] == []):
                Memory.worker_paths[unit.id] = Constants.DESTINATION_REACHED
            return
        else:
            if not gc.is_move_ready(unit.id):
                placeholder = True
            else:
                try:
                    Memory.worker_turns_stuck[unit.id] += 1
                except:
                    Memory.worker_turns_stuck[unit.id] = 1
                return
    except:
        for i in np.random.permutation(8):
            myDirection = directions[i]
            if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                gc.move_robot(unit.id, myDirection)
                return

#basic logic for workers on mars
def MarsWorkerLogic(unit):
    if inDanger(unit):
        successful = tryToMoveToSafety(unit)
        if successful:
            return

    for i in np.random.permutation(8):
        myDirection = directions[i]
        if gc.can_harvest(unit.id, myDirection):
            gc.harvest(unit.id, myDirection)
            harvestedLoc = locFromDirect(unit, myDirection)
            karboniteMapMars[(harvestedLoc.x, harvestedLoc.y)] = gc.karbonite_at(harvestedLoc)
        elif gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            return

#basic logic for healers on mars
def MarsHealerLogic(unit):
    if inDanger(unit):
        successful = tryToMoveToSafety(unit)
        if successful:
            return

    nearby = gc.sense_nearby_units(location.map_location(), Constants.HEALER_VISION)

    lowestHealth = 1000
    unitToHeal = unit

    
    #heal the unit on our team that is most injured
    for place in nearby:

        if place.team == my_team:
            if place.health < lowestHealth:
                lowestHealth = place.health
                unitToHeal = place

    if unitToHeal != unit:
        if gc.is_heal_ready(unit.id) and gc.can_heal(unit.id, unitToHeal.id):
            gc.heal(unit.id, unitToHeal.id)
            return


    myDirection = directions[random.randint(0, 7)]
    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
        gc.move_robot(unit.id, myDirection)
        return

#Combat logic on mars
def MarsCombatLogic(unit):
    if unit.id not in Memory.combat_destinations:
        point = (unit.location.map_location().x, unit.location.map_location().y)
        potentials = invertPoint(point, bc.Planet.Mars)
        randNum = random.randint(0, len(potentials) - 1)
        Memory.combat_destinations[unit.id] = potentials[randNum]


    if inDanger(unit):
        successful = tryToMoveToSafety(unit)

    if unit.unit_type == bc.UnitType.Mage:
        nearby = gc.sense_nearby_units(location.map_location(), Constants.MAGE_VISION)
    elif unit.unit_type == bc.UnitType.Ranger:
        nearby = gc.sense_nearby_units(location.map_location(), Constants.RANGER_VISION)

    minHealth = 1000
    killableEnemy = unit
    mostDangerousEnemy = unit
    distToDangerous = 1000
    myLoc = unit.location.map_location()
    nonAggressiveUnits = []

    for place in nearby:
        if place.team != my_team:
            tempLoc = place.location.map_location()
            distTo = pow(tempLoc.x - myLoc.x, 2) + pow(tempLoc.y - myLoc.y, 2)
            if place.health < minHealth:
                minHealth = place.health
                if minHealth < unit.damage():
                    killableEnemy = place

            if place.unit_type in Constants.DANGEROUS_ENEMIES:
                if distTo < distToDangerous:
                    mostDangerousEnemy = place
                    distToDangerous = distTo
            else:
                nonAggressiveUnits.append(place)

    if killableEnemy != unit:
        if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, killableEnemy.id):
            gc.attack(unit.id, killableEnemy.id)

    elif mostDangerousEnemy != unit:
        if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, mostDangerousEnemy.id):
            gc.attack(unit.id, mostDangerousEnemy.id)
    elif len(nonAggressiveUnits) > 0:
        if len(nonAggressiveUnits) == 1:
            if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, nonAggressiveUnits[0].id):
                gc.attack(unit.id, nonAggressiveUnits[0].id)
        else:
            choice = random.randint(0, len(nonAggressiveUnits) - 1)
            chosenEnemy = nonAggressiveUnits[choice]
            if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, chosenEnemy.id):
                gc.attack(unit.id, chosenEnemy.id)
    else:
        for enemy in Memory.current_vision_earth:
            enemyLoc = bc.MapLocation(myLoc.planet, enemy[0], enemy[1])
            distTo = max(enemyLoc.x - myLoc.x, enemyLoc.y - myLoc.y)
            if distTo < 10:
                myDirection = myLoc.direction_to(enemyLoc)
                change = Constants.CHANGE_FROM_DIRECT[myDirection]
                potentialSpot = bc.MapLocation(myLoc.planet, myLoc.x + change[0], myLoc.y + change[1])
                if not dangerousSpot(potentialSpot) and gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return

        #Code for moving around on mars
        curPlanet = unit.location.map_location().planet

        destination = bc.MapLocation(curPlanet, Memory.combat_destinations[unit.id][0],
                                     Memory.combat_destinations[unit.id][1])

        try:
            # get the destination that this unit is supposed to be going to
            path = Memory.combat_paths[unit.id]
            # if we already reached that destination: get a new one
            if path == Constants.DESTINATION_REACHED:
                if gc.is_move_ready(unit.id):
                    for i in np.random.permutation(8):
                        myDirection = directions[i]
                        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                            gc.move_robot(unit.id, myDirection)
                            return

        except:
            # this will only happen the first time a destination is generated for a spot
            path = BFS_firstStep(unit, destination)


            Memory.combat_paths[unit.id] = path

        # move in the correct direction to get to our destination if possible.
        try:
            nextStep = bc.MapLocation(unit.location.map_location().planet, path[0][0], path[0][1])
        except:
            for i in np.random.permutation(8):
                myDirection = directions[i]
                if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return

        myDirection = unit.location.map_location().direction_to(nextStep)

        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            # remove the first step of the path that we had.

            Memory.combat_paths[unit.id] = path[1:]
            if len(Memory.combat_paths[unit.id]) == 1:
                Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED
            return
        else:
            if not gc.is_move_ready(unit.id):
                placeholder = True
            else:
                for i in np.random.permutation(8):
                    myDirection = directions[i]
                    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                        gc.move_robot(unit.id, myDirection)
                        return

#returns the attack range for a given unit
def getAttackRange(unit):
    if unit.unit_type == bc.UnitType.Ranger:
        return Constants.RANGER_RANGE
    elif unit.unit_type == bc.UnitType.Mage:
        return Constants.MAGE_RANGE
    elif unit.unit_type == bc.UnitType.Knight:
        return Constants.KNIGHT_RANGE
    else:
        return 0


# method used to check if a spot will be dangerous before moving there - very similar to inDanger
def dangerousSpot(location):
    ourLoc = location

    for key in Memory.current_vision_earth:
        enemyUnit = Memory.current_vision_earth[key]
        enemyLoc = enemyUnit.location.map_location()
        #add two to the range because if a enemyUnit could easily move into position to attack
        #this spot it should be treated as dangerous
        enemyRange = getAttackRange(enemyUnit) + 2
        distTo = pow(enemyLoc.x - ourLoc.x, 2) + pow(enemyLoc.y - ourLoc.y, 2)
        if enemyUnit.unit_type == bc.UnitType.Ranger:
            if distTo > 10 and distTo <= enemyRange:
                return True
        else:
            if distTo <= enemyRange:
                return True
    return False

def inDanger(unit):
    ourLoc = unit.location.map_location()

    for key in Memory.current_vision_earth:
        enemyUnit = Memory.current_vision_earth[key]
        enemyLoc = enemyUnit.location.map_location()
        #add two to the range because if a enemyUnit could easily move into position to attack
        #this spot it should be treated as dangerous
        enemyRange = getAttackRange(enemyUnit) + 2
        distTo = pow(enemyLoc.x - ourLoc.x, 2) + pow(enemyLoc.y - ourLoc.y, 2)
        if enemyUnit.unit_type == bc.UnitType.Ranger:
            if distTo > 10 and distTo <= enemyRange:
                return True
        else:
            if distTo <= enemyRange:
                return True
    return False

#if a unit is in danger, try to move it to the safest spot it will survive in
def tryToMoveToSafety(unit):
    toCheck = getNeighbors(unit.location.map_location())
    toCheck.append(unit.location.map_location())

    #only check spots that we are able to move to
    for spot in list(toCheck):
        if not gc.is_occupiable(spot) and spot != unit.location.map_location():
            toCheck.remove(spot)

    ourLoc = unit.location.map_location()

    damageDict = {}
    # initialize dictionary
    for spot in toCheck:
        damageDict[(spot.x, spot.y)] = 0

    #go through every enemy unit, looking for ones that could attack us.  if they can attack this spot
    #add their damage to the damage dictionary for that spot
    for key in Memory.current_vision_earth:
        enemyUnit = Memory.current_vision_earth[key]
        enemyType = enemyUnit.unit_type
        if enemyType in Constants.DANGEROUS_ENEMIES:
            enemyRange = getAttackRange(enemyUnit)
            enemyLoc = enemyUnit.location.map_location()
            if pow(ourLoc.x - enemyLoc.x, 2) + pow(ourLoc.y - enemyLoc.y, 2) < 55:
                for spot in toCheck:
                    distTo = pow(spot.x - enemyLoc.x, 2) + pow(spot.y - enemyLoc.y, 2)
                    if enemyType == bc.UnitType.Ranger:
                        if distTo <= enemyRange and distTo > 10:
                            damageDict[(spot.x, spot.y)] += enemyUnit.damage()
                    else:
                        if distTo <= enemyRange:
                            damageDict[(spot.x, spot.y)] += enemyUnit.damage()
    # damageDict will now list the damage we will take at any one of these spots
    minDamage = 10000
    bestSpots = []
    for spot in toCheck:
        if damageDict[(spot.x, spot.y)] < minDamage:
            minDamage = damageDict[spot.x, spot.y]
            bestSpots = [spot]
        elif damageDict[spot.x, spot.y] == minDamage:
            bestSpots.append(spot)


    if minDamage > unit.health:
        # this means we die no matter where we move, so we might as well not try to.
        return False
    else:
        #pick one of potentialy many best spots and move to it
        randNum = 0
        if len(bestSpots) > 1:
            randNum = random.randint(0, len(bestSpots) - 1)

        chosenSpot = bestSpots[randNum]
        myDirection = unit.location.map_location().direction_to(chosenSpot)
        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            if unit.unit_type == bc.UnitType.Worker:
                Memory.worker_paths[unit.id] = Constants.DESTINATION_REACHED
            else:
                Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED
            return True
        return False


def WorkerLogic(unit):
    # priorities should be:
    # escape from enemies
    # replicate if we need more workers
    # harvest karbonite if near it / build structures if near it
    # move towards karbonite / nearest unbuilt structure

    # code to escape from enemies close
    if inDanger(unit):
        successful = tryToMoveToSafety(unit)
        if successful:
            return

    #if we're being sent to mars do that for sure
    if MyVars.rocketCount > 0 and unit.id in Memory.marsTroops and unit.location.map_location().planet == bc.Planet.Earth:
        if unit.id not in Memory.rocket_destination:
            rocketFound = False
            nearby = gc.sense_nearby_units(location.map_location(), Constants.WKH_VISION)
            for place in nearby:
                if place.team == my_team and place.unit_type == bc.UnitType.Rocket:
                    rocketFound = True
                    Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,
                                                                        place.location.map_location().x + 1,
                                                                        place.location.map_location().y)

            if not rocketFound:
                randNum = random.randint(0, len(MyVars.rocketLocations) - 1)
                Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth, MyVars.rocketLocations[
                    randNum].x + 1, MyVars.rocketLocations[randNum].y)

        if bc.MapLocation(bc.Planet.Earth, Memory.rocket_destination[unit.id].x -1, Memory.rocket_destination[unit.id].y) not in MyVars.rocketLocations or MyVars.rocketCount == 0:
            Memory.marsTroops.remove(unit.id)
        else:
            moveMarsUnit(unit)
            return

    if unit.location.map_location().planet == bc.Planet.Mars:
        MarsWorkerLogic(unit)
        return

    # if we have reached our destination, change this units destination to a placeholder representing
    # that it has been reached.
    
    else:
        
        # get locations which are passable nearby
        validLocs = getNeighbors(unit.location.map_location())
        
        #this is time to start building as many rockets as humanly possible
        if gc.round() > 600:
            nearby = gc.sense_nearby_units(unit.location.map_location(), 2)
            for tempUnit in nearby:
                if gc.can_build(unit.id, tempUnit.id):
                    gc.build(unit.id, tempUnit.id)
                    return
                else:
                    if tempUnit.unit_type == bc.UnitType.Rocket:
                        #we want to stay near it and not try to build anything else till this is done
                        return
            if gc.karbonite() > Constants.ROCKET_COST:
                for loc in validLocs:
                    tempScore = evalFactorySpot(loc)
                    #we'll loosen standards since we're trying to get out of here asap
                    if tempScore > 0:
                        directTo = unit.location.map_location().direction_to(loc)
                        if gc.can_blueprint(unit.id, bc.UnitType.Factory, directTo):
                            gc.blueprint(unit.id, bc.UnitType.Rocket, directTo)
                            MyVars.rocketCount += 1
                            MyVars.rocketLocations.append(loc)
                            return
            #we need workers to make rockets but dont want too many at this point
            if MyVars.workerCount <= 3 and gc.karbonite() >= Constants.REPLICATE_COST:
                direct = getNeighbors(unit.location.map_location())
                for i in range(len(direct)):
                    direction = unit.location.map_location().direction_to(direct[i])
                    if gc.can_replicate(unit.id, direction):
                        gc.replicate(unit.id, direction)
                        MyVars.workerCount += 1
            #at this point in the game they're just going to wait around until they can build
            return
        
        
        if MyVars.workerCount < Constants.DESIRED_WORKERS and gc.karbonite() >= Constants.REPLICATE_COST:
            direct = getNeighbors(unit.location.map_location())
            for i in range(len(direct)):
                direction = unit.location.map_location().direction_to(direct[i])
                if gc.can_replicate(unit.id, direction):
                    gc.replicate(unit.id, direction)
                    MyVars.workerCount += 1

        # get nearby units and build them if possible
        nearby = gc.sense_nearby_units(unit.location.map_location(), 2)
        for tempUnit in nearby:
            if gc.can_build(unit.id, tempUnit.id):
                gc.build(unit.id, tempUnit.id)
                return

        # try to build a rocket blueprint if we have enough karbonite and troops

        if gc.karbonite() > Constants.ROCKET_COST and MyVars.rocketCount < Constants.DESIRED_ROCKETS and len(
                gc.my_units()) > 32:
            bestScore = -100000
            bestScoreLoc = unit.location.map_location()
            for loc in validLocs:
                tempScore = evalFactorySpot(loc)
                if tempScore > bestScore:
                    bestScore = tempScore
                    bestScoreLoc = loc

            if bestScore > 50:
                directTo = unit.location.map_location().direction_to(bestScoreLoc)
                if gc.can_blueprint(unit.id, bc.UnitType.Factory, directTo):
                    gc.blueprint(unit.id, bc.UnitType.Rocket, directTo)
                    MyVars.rocketCount += 1
                    MyVars.rocketLocations.append(bestScoreLoc)
                    return

        # try to build a factory blueprint if we don't have enough and have sufficient karbonite
        if gc.karbonite() > Constants.FACTORY_COST and MyVars.factoryCount < Constants.DESIRED_FACTORIES:

            bestScore = -100000
            bestScoreLoc = unit.location.map_location()
            for loc in validLocs:
                tempScore = evalFactorySpot(loc)
                if tempScore > bestScore:
                    bestScore = tempScore
                    bestScoreLoc = loc

            if bestScore > 50:
                directTo = unit.location.map_location().direction_to(bestScoreLoc)
                if gc.can_blueprint(unit.id, bc.UnitType.Factory, directTo):
                    gc.blueprint(unit.id, bc.UnitType.Factory, directTo)
                    MyVars.factoryCount += 1
                    MyVars.factoryLocations.append(bestScoreLoc)
                    return

        # if we're close enough to our destination, harvest any karbonite that is near us
        #we want to be close so we dont hold up an entire line of workers
        distToDest = 0
        try:
            if Memory.worker_paths[unit.id] == Constants.DESTINATION_REACHED:
                distToDest = 0
            else:
                tempDest = Memory.worker_paths[unit.id][-1]
                distToDest = pow(tempDest[0] - unit.location.map_location().x, 2) + pow(
                    tempDest[1] - unit.location.map_location().y, 2)
        except:
            distToDest = 0
        if distToDest < 5:

            for direct in directions:
                if gc.can_harvest(unit.id, direct):
                    gc.harvest(unit.id, direct)
                    harvestedLoc = locFromDirect(unit, direct)

                    # if this one is here harvesting, then make sure that other ones go somewhere else
                    for key in Memory.worker_paths:
                        try:
                            if (harvestedLoc.x, harvestedLoc.y) == Memory.worker_paths[key][-1]:
                                Memory.worker_paths[key] = Constants.DESTINATION_REACHED
                        except:
                            placeHolder = True

                    if unit.location.map_location().planet == bc.Planet.Earth:

                        if (gc.karbonite_at(harvestedLoc) < 1):
                            try:
                                del karboniteMapEarth[(harvestedLoc.x, harvestedLoc.y)]
                            except:
                                placeHolder = True
                        else:
                            karboniteMapEarth[(harvestedLoc.x, harvestedLoc.y)] = gc.karbonite_at(harvestedLoc)
                    else:
                        karboniteMapMars[harvestedLoc.x][harvestedLoc.y] = gc.karbonite_at(harvestedLoc)
                    return

        #only bother moving to new karbonite if we have some karbonite left on the map
        if len(karboniteMapEarth) > 0:
            
            try:
                if (unit.location.map_location().x, unit.location.map_location().y) == Memory.worker_paths[unit.id][-1]:
                    Memory.worker_paths[unit.id] = Constants.DESTINATION_REACHED
            except:
                if gc.get_time_left_ms() > 3000:

                    # do nothing - here so that we don't get an error if we haven't calculated a path yet
                    destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)
                    path = BFS_firstStep(unit, destination)
                    Memory.worker_paths[unit.id] = path
                    # if we don't have enough workers,

            moveWorker(unit)
        else:
            #move randomly
            for i in np.random.permutation(8):
                myDirection = directions[i]
                if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return

#used to try to map out what karbonite is feasibly harvestable by us and which isnt
def karbMultiplier(location):
    minDistEnemy = 1000000
    minDistFriendly = 1000000

    for spot in Constants.START_POINTS:
        tempDist = math.sqrt(pow(location.x - spot[0], 2) + pow(location.y - spot[1], 2))
        if tempDist < minDistFriendly:
            minDistFriendly = tempDist

    #if we're spread out around the map we want to look at smaller places around where each person
    #starts
    differentStartLocations = 1
    if len(Constants.START_POINTS) > 0:
        firstStart = Constants.START_POINTS[0]
        if len(Constants.START_POINTS) > 0:
            for i in range(1,len(Constants.START_POINTS)):
                temp = Constants.START_POINTS[i]
                if pow(temp[0] - firstStart[0], 2) + pow(temp[1] - firstStart[1], 2) > 90:
                    differentStartLocations+=1
    
    if differentStartLocations >= 3:
        if minDistFriendly > 10:
            return 0
    elif differentStartLocations == 2:
        if minDistFriendly > 15:
            return 0
    elif differentStartLocations == 1:
        if minDistFriendly > 25:
            return 0

    #if the karbonite isnt reachable automatically ignore it
    reachable = False
    for cluster in Memory.reachable_clusters:
        if (location.x, location.y) in cluster:
            reachable = True

    if reachable:
        return 1
    else:
        return 0

#picks a rocket destination from the potential landing spots
def getRocketDestination(unit):
    
    if len(possibleLandingSpots) == 1:
        chosenSpot = possibleLandingSpots[0]
        return bc.MapLocation(bc.Planet.Mars, chosenSpot[0], chosenSpot[1])
    else:
        choice = random.randint(0,len(possibleLandingSpots) -1)
        chosenSpot = possibleLandingSpots[choice]
        return bc.MapLocation(bc.Planet.Mars, chosenSpot[0], chosenSpot[1])


def rocket_logic(unit):
    garrison = unit.structure_garrison()
    if unit.location.map_location().planet == bc.Planet.Earth:
        destination = getRocketDestination(unit)
        #get off earth asap if its close to the flood
        if gc.round() > 740:
            if gc.can_launch_rocket(unit.id, destination):
                gc.launch_rocket(unit.id, destination)
                MyVars.rocketLocations.remove(unit.location.map_location())
                MyVars.rocketCount -= 1
         #if we're being attacked get out of there
        if inDanger(unit):
            if len(garrison) > 0:
                if gc.can_launch_rocket(unit.id, destination):
                    gc.launch_rocket(unit.id, destination)
                    MyVars.rocketLocations.remove(unit.location.map_location())
                    MyVars.rocketCount -= 1
 
                else:
                    gc.disintegrate_unit(unit.id)
                    MyVars.rocketLocations.remove(unit.location.map_location())
                    MyVars.rocketCount -= 1
        #try to load units if we're not full
        elif len(garrison) < 8:
            nearby = gc.sense_nearby_units(location.map_location(), Constants.ROCKET_VISION)
            for place in nearby:
                if place.team == my_team and gc.can_load(unit.id, place.id):
                    gc.load(unit.id, place.id)
        #if we're full, launch
        elif gc.can_launch_rocket(unit.id, destination):
            gc.launch_rocket(unit.id, destination)
            MyVars.rocketLocations.remove(unit.location.map_location())
            MyVars.rocketCount -= 1
        
    elif unit.location.map_location().planet == bc.Planet.Mars:
        #unload units
        if len(garrison) > 0:
            d = random.choice(directions)
            if gc.can_unload(unit.id, d):
                gc.unload(unit.id, d)
        else:
            gc.disintegrate_unit(unit.id)


def ranger_logic(unit):
    #move towards our rocket if we're being sent to mars
    if unit.id in Memory.marsTroops and unit.location.map_location().planet == bc.Planet.Earth and MyVars.rocketCount > 0:
        if unit.id not in Memory.rocket_destination:
            rocketFound = False
            nearby = gc.sense_nearby_units(location.map_location(), Constants.RANGER_VISION)
            for place in nearby:
                if place.team == my_team and place.unit_type == bc.UnitType.Rocket:
                    rocketFound = True
                    Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,
                                                                        place.location.map_location().x + 1,
                                                                        place.location.map_location().y)

            if not rocketFound:
                randNum = random.randint(0, len(MyVars.rocketLocations) - 1)
                Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,
                                                                    MyVars.rocketLocations[randNum].x + 1,
                                                                    MyVars.rocketLocations[randNum].y)

        if bc.MapLocation(bc.Planet.Earth, Memory.rocket_destination[unit.id].x -1, Memory.rocket_destination[unit.id].y) not in MyVars.rocketLocations or MyVars.rocketCount == 0:
            Memory.marsTroops.remove(unit.id)
        else:
            moveMarsUnit(unit)
            return

    if unit.location.map_location().planet == bc.Planet.Mars:
        MarsCombatLogic(unit)
        return

    #pick a random enemy starting location to go to initially.  make sure that its in a cluster
    #that we can reach.  if none of the starting locations are reachable, let the entire group know
    #and just start moving randomly
    if unit.id not in Memory.combat_destinations and not Constants.ENEMIES_UNREACHABLE:
        Memory.combat_destinations[unit.id] = (100, 100)

        # try to get a destination
        randNum = random.randint(0, len(Constants.ENEMY_START_POINTS) - 1)
        myLocation = unit.location.map_location()
        myCluster = []
        for cluster in Memory.reachable_clusters:
            if (myLocation.x, myLocation.y) in cluster:
                myCluster = cluster
        for i in np.random.permutation(len(Constants.ENEMY_START_POINTS)):
            enPoint = Constants.ENEMY_START_POINTS[i]
            if enPoint in myCluster:
                Memory.combat_destinations[unit.id] = Constants.ENEMY_START_POINTS[i]
                i = len(Constants.ENEMY_START_POINTS) + 1
        if Memory.combat_destinations[unit.id] == (100, 100):
            Constants.ENEMIES_UNREACHABLE = True
            Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED

    elif Constants.ENEMIES_UNREACHABLE:
        Memory.combat_destinations[unit.id] = (100, 100)
        Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED
    else:
        Memory.combat_destinations[unit.id] = (100, 100)

    #get out of danger if we can
    if inDanger(unit):
        successful = tryToMoveToSafety(unit)

    nearby = gc.sense_nearby_units(location.map_location(), Constants.RANGER_RANGE)

    minHealth = 1000
    killableEnemy = unit
    mostDangerousEnemy = unit
    distToDangerous = 1000
    myLoc = unit.location.map_location()
    tooCloseEnemies = []
    nonAggressiveUnits = []

    #map out all of the enemy units around us into their listings
    for place in nearby:
        if place.team != my_team:
            tempLoc = place.location.map_location()
            distTo = pow(tempLoc.x - myLoc.x, 2) + pow(tempLoc.y - myLoc.y, 2)
            if distTo > 10:
                if place.health < minHealth:
                    minHealth = place.health
                    if minHealth < unit.damage():
                        killableEnemy = place

                if place.unit_type in Constants.DANGEROUS_ENEMIES:
                    if distTo < distToDangerous:
                        mostDangerousEnemy = place
                        distToDangerous = distTo
                else:
                    nonAggressiveUnits.append(place)
            else:
                tooCloseEnemies.append(place)

    #our first priority should always be to kill enemies
    if killableEnemy != unit:
        # if the unit can attack the enemy and is ready to attack then attack the enemy
        if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, killableEnemy.id):
            gc.attack(unit.id, killableEnemy.id)
    #next, we always prioritize killing dangerous enemies and attack the closest one
    elif mostDangerousEnemy != unit:
        if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, mostDangerousEnemy.id):
            gc.attack(unit.id, mostDangerousEnemy.id)
    #if there are none of both of these, we attack the closest factory, worker, healer or rocket
    elif len(nonAggressiveUnits) > 0:
        if len(nonAggressiveUnits) == 1:
            if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, nonAggressiveUnits[0].id):
                gc.attack(unit.id, nonAggressiveUnits[0].id)
        else:
        #choose a non-aggressive unit to attack and try to attack it
            choice = random.randint(0, len(nonAggressiveUnits) - 1)
            chosenEnemy = nonAggressiveUnits[choice]
            if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, chosenEnemy.id):
                gc.attack(unit.id, chosenEnemy.id)
    elif len(tooCloseEnemies) > 0:
        #move away from enemys that are too close for comfort for rangers
        for i in np.random.permutation(len(tooCloseEnemies)):

            chosenEnemy = tooCloseEnemies[i]
            myDirection = invertDirection(myLoc.direction_to(chosenEnemy.location.map_location()))
            if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                gc.move_robot(unit.id, myDirection)
                return
    else:
        #if we have vision on enemies, try to move towards them
        for enemy in Memory.current_vision_earth:
            enemyLoc = bc.MapLocation(myLoc.planet, enemy[0], enemy[1])
            distTo = max(enemyLoc.x - myLoc.x, enemyLoc.y - myLoc.y)
            if distTo < 10:
                myDirection = myLoc.direction_to(enemyLoc)
                change = Constants.CHANGE_FROM_DIRECT[myDirection]
                potentialSpot = bc.MapLocation(myLoc.planet, myLoc.x + change[0], myLoc.y + change[1])
                if not dangerousSpot(potentialSpot) and gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return
        #if none of the other stuff happens, then move on to the move combat unit function
        moveCombatUnit(unit)

#same exact thing as ranger logic except for we dont worry about a min attack range
def mage_logic(unit):
    if unit.id in Memory.marsTroops and unit.location.map_location().planet == bc.Planet.Earth and MyVars.rocketCount > 0:
        if unit.id not in Memory.rocket_destination:
            rocketFound = False
            nearby = gc.sense_nearby_units(location.map_location(), Constants.MAGE_VISION)
            for place in nearby:
                if place.team == my_team and place.unit_type == bc.UnitType.Rocket:
                    rocketFound = True
                    Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,
                                                                        place.location.map_location().x + 1,
                                                                        place.location.map_location().y)

            if not rocketFound:
                randNum = random.randint(0, len(MyVars.rocketLocations) - 1)
                Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,
                                                                    MyVars.rocketLocations[randNum].x + 1,
                                                                    MyVars.rocketLocations[randNum].y)

        if bc.MapLocation(bc.Planet.Earth, Memory.rocket_destination[unit.id].x -1, Memory.rocket_destination[unit.id].y) not in MyVars.rocketLocations or MyVars.rocketCount == 0:
            Memory.marsTroops.remove(unit.id)
        else:
            moveMarsUnit(unit)
            return


    if unit.location.map_location().planet == bc.Planet.Mars:
        MarsCombatLogic(unit)
        return

    if unit.id not in Memory.combat_destinations and not Constants.ENEMIES_UNREACHABLE:
        Memory.combat_destinations[unit.id] = (100, 100)

        # try to get a destination
        randNum = random.randint(0, len(Constants.ENEMY_START_POINTS) - 1)
        myLocation = unit.location.map_location()
        myCluster = []
        for cluster in Memory.reachable_clusters:
            if (myLocation.x, myLocation.y) in cluster:
                myCluster = cluster
        for i in np.random.permutation(len(Constants.ENEMY_START_POINTS)):
            enPoint = Constants.ENEMY_START_POINTS[i]
            if enPoint in myCluster:
                Memory.combat_destinations[unit.id] = Constants.ENEMY_START_POINTS[i]
                i = len(Constants.ENEMY_START_POINTS) + 1
        if Memory.combat_destinations[unit.id] == (100, 100):
            Constants.ENEMIES_UNREACHABLE = True
            Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED

    elif Constants.ENEMIES_UNREACHABLE:
        Memory.combat_destinations[unit.id] = (100, 100)
        Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED
    else:
        Memory.combat_destinations[unit.id] = (100, 100)

    if inDanger(unit):
        successful = tryToMoveToSafety(unit)

    nearby = gc.sense_nearby_units(location.map_location(), Constants.MAGE_RANGE)

    minHealth = 1000
    killableEnemy = unit
    mostDangerousEnemy = unit
    distToDangerous = 1000
    myLoc = unit.location.map_location()
    nonAggressiveUnits = []

    for place in nearby:
        if place.team != my_team:
            tempLoc = place.location.map_location()
            distTo = pow(tempLoc.x - myLoc.x, 2) + pow(tempLoc.y - myLoc.y, 2)
            if place.health < minHealth:
                minHealth = place.health
                if minHealth < unit.damage():
                    killableEnemy = place

            if place.unit_type in Constants.DANGEROUS_ENEMIES:
                if distTo < distToDangerous:
                    mostDangerousEnemy = place
                    distToDangerous = distTo
            else:
                nonAggressiveUnits.append(place)

    if killableEnemy != unit:
         # if the unit can attack the enemy and it will die and is ready to attack then attack the enemy
        if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, killableEnemy.id):
            gc.attack(unit.id, killableEnemy.id)

    elif mostDangerousEnemy != unit:
         # if the unit can attack the enemy and is ready to attack then attack the enemy
        if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, mostDangerousEnemy.id):
            gc.attack(unit.id, mostDangerousEnemy.id)
    elif len(nonAggressiveUnits) > 0:
        #choose a non-aggressive unit to attack and try to attack it
        if len(nonAggressiveUnits) == 1:
            if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, nonAggressiveUnits[0].id):
                gc.attack(unit.id, nonAggressiveUnits[0].id)
        else:
            choice = random.randint(0, len(nonAggressiveUnits) - 1)
            chosenEnemy = nonAggressiveUnits[choice]
            if gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, chosenEnemy.id):
                gc.attack(unit.id, chosenEnemy.id)
    else:
        for enemy in Memory.current_vision_earth:
            enemyLoc = bc.MapLocation(myLoc.planet, enemy[0], enemy[1])
            distTo = max(enemyLoc.x - myLoc.x, enemyLoc.y - myLoc.y)
            if distTo < 10:
                myDirection = myLoc.direction_to(enemyLoc)
                change = Constants.CHANGE_FROM_DIRECT[myDirection]
                potentialSpot = bc.MapLocation(myLoc.planet, myLoc.x + change[0], myLoc.y + change[1])
                if not dangerousSpot(potentialSpot) and gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return
        #if none of the other stuff happens, then move on to the move combat unit function
        moveCombatUnit(unit)

#move randomly around the map and heal low health workers if possible.
def healer_logic(unit):
    global healCount

    if unit.id in Memory.marsTroops and unit.location.map_location().planet == bc.Planet.Earth and MyVars.rocketCount > 0:
        if unit.id not in Memory.rocket_destination:
            rocketFound = False
            nearby = gc.sense_nearby_units(location.map_location(), Constants.HEALER_VISION)
            for place in nearby:
                if place.team == my_team and place.unit_type == bc.UnitType.Rocket:
                    rocketFound = True
                    Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,
                                                                        place.location.map_location().x + 1,
                                                                        place.location.map_location().y)

            if not rocketFound:
                randNum = random.randint(0, len(MyVars.rocketLocations) - 1)
                Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,
                                                                    MyVars.rocketLocations[randNum].x + 1,
                                                                    MyVars.rocketLocations[randNum].y)

        if bc.MapLocation(bc.Planet.Earth, Memory.rocket_destination[unit.id].x -1, Memory.rocket_destination[unit.id].y) not in MyVars.rocketLocations or MyVars.rocketCount == 0:
            Memory.marsTroops.remove(unit.id)
        else:
            moveMarsUnit(unit)
            return

    if unit.location.map_location().planet == bc.Planet.Mars:
        MarsHealerLogic(unit)
        return

    if inDanger(unit):
        successful = tryToMoveToSafety(unit)
        if successful:
            return

    nearby = gc.sense_nearby_units(location.map_location(), Constants.HEALER_VISION)

    lowestHealth = 1000
    unitToHeal = unit

    for place in nearby:

        if place.team == my_team:
            if place.health < lowestHealth:
                lowestHealth = place.health
                unitToHeal = place

    if unitToHeal != unit:
        if gc.is_heal_ready(unit.id) and gc.can_heal(unit.id, unitToHeal.id):
            healCount += 1
            gc.heal(unit.id, unitToHeal.id)
            return


    myDirection = directions[random.randint(0, 7)]
    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
        gc.move_robot(unit.id, myDirection)
        return


def factory_logic(unit):
    garrison = unit.structure_garrison()
    if len(garrison) > 0:
        d = random.choice(directions)
        if gc.can_unload(unit.id, d):
            gc.unload(unit.id, d)
            return
    #the production of units is determined by the weight of the unit. a random number is selected from 0 to the combined weight of the units.
    #the number determins which kind of unit will be produced. The higher the weight of the unit, the greater chance it will be produced.
    # healer weight is increased until it reaches its max weight so that more healers are produced later in the game than at the begining
    #if we are critically low on workers we produce them
    
    #if the round is greater than 600, we want to prioritize making rockets so we dont put out units
    #unless we have a ton of karbonite
    
    if gc.round() < 600 or gc.karbonite() > 300:
        if MyVars.workerCount < 3 and gc.can_produce_robot(unit.id, bc.UnitType.Worker):
            gc.produce_robot(unit.id, bc.UnitType.Worker)
        elif gc.can_produce_robot(unit.id, bc.UnitType.Ranger):
            toproduce = random.randint(0, (MyVars.mageWeight + MyVars.rangerWeight + MyVars.healerWeight))
            if toproduce <= MyVars.rangerWeight:
                gc.produce_robot(unit.id, bc.UnitType.Ranger)
                return
            elif toproduce <= (MyVars.mageWeight + MyVars.rangerWeight):
                gc.produce_robot(unit.id, bc.UnitType.Mage)
                return
            elif toproduce <= (MyVars.mageWeight + MyVars.rangerWeight + MyVars.healerWeight):
                gc.produce_robot(unit.id, bc.UnitType.Healer)
                return

###INITIAL SETUP###


# get initial variables and maps

gc.queue_research(bc.UnitType.Worker)
gc.queue_research(bc.UnitType.Rocket)
gc.queue_research(bc.UnitType.Mage)
gc.queue_research(bc.UnitType.Ranger)
gc.queue_research(bc.UnitType.Ranger)
gc.queue_research(bc.UnitType.Mage)
gc.queue_research(bc.UnitType.Mage)
gc.queue_research(bc.UnitType.Worker)
gc.queue_research(bc.UnitType.Worker)


directions = list(bc.Direction)

earthMap = gc.starting_map(bc.Planet.Earth)
marsMap = gc.starting_map(bc.Planet.Mars)

earthWidth = earthMap.width
earthHeight = earthMap.height



marsWidth = marsMap.width
marsHeight = marsMap.height

# create maps of what places are passable and what places have karbonite on them
karboniteMapEarth = {}
karboniteMapMars = {}
passableMapEarth = []
passableMapMars = []
possibleLandingSpots = []

# create the shells of the maps
for i in range(earthWidth):
    passableMapEarth.append([False] * earthHeight)

for i in range(marsWidth):
    passableMapMars.append([False] * marsHeight)
    #possibleLandingSpots.append([False] * marsHeight)

totalCount = 0

mapReachable()

# get all of our starting points as well as the likely enemy starting points


for unit in gc.my_units():
    loc = unit.location.map_location()
    temp = (loc.x, loc.y)
    Constants.START_POINTS.append(temp)

for point in Constants.START_POINTS:
    potentials = invertPoint(point, bc.Planet.Earth)
    for spot in potentials:
        Constants.ENEMY_START_POINTS.append(spot)

# add in numbers/booleans for where karbonite/passable terrain is.
for i in range(earthWidth):
    for j in range(earthHeight):
        loc = bc.MapLocation(bc.Planet.Earth, i, j)
        karbCount = int(earthMap.initial_karbonite_at(loc)) * karbMultiplier(loc)
        if (karbCount > 0):
            totalCount += karbCount
            karboniteMapEarth[(i, j)] = int(earthMap.initial_karbonite_at(loc))
        passableMapEarth[i][j] = earthMap.is_passable_terrain_at(loc)


for i in range(marsWidth):
    for j in range(marsHeight):
        loc = bc.MapLocation(bc.Planet.Mars, i, j)
        karbCount = int(marsMap.initial_karbonite_at(loc))
        if (karbCount > 0):
            karboniteMapMars[(i, j)] = int(marsMap.initial_karbonite_at(loc))
        passableMapMars[i][j] = marsMap.is_passable_terrain_at(loc)
        try:
            if marsMap.is_passable_terrain_at(loc):
                possibleLandingSpots.append((i,j))
        except:
            placeholder = True

# now, on earth, try to scale the amount of karbonite so that places close to the enemy aren't listed as
# having any.  Also, remove any places that are unreachable by our people.
Constants.INITIAL_KARB_COUNT = totalCount

minSize = 10000
maxSize = -10000

for cluster in Memory.reachable_clusters:
    if len(cluster) > maxSize:
        maxSize = len(cluster)
    if len(cluster) < minSize:
        minSize = len(cluster)

if maxSize == minSize:
    if maxSize >= 200:
        MyVars.rangerWeight = 45
        MyVars.mageWeight = 30
    else:
        MyVars.rangerWeight = 30
        MyVars.mageWeight = 45
else:
    if minSize < 150:
        MyVars.mageWeight = 45
    elif minSize < 200:
        MyVars.mageWeight = 40
    else:
        MyVars.mageWeight = 30

    if maxSize > 700:
        MyVars.rangerWeight = 55
    elif maxSize > 550:
        MyVars.rangerWeight = 50
    elif maxSize > 475:
        MyVars.rangerWeight = 45
    else:
        MyVars.rangerWeight = 30


while True:
    # We only support Python 3, which means brackets around print()
    print('pyround:', gc.round(), 'time left:', gc.get_time_left_ms(), 'ms')
    # frequent try/catches are a good idea
    try:
        #increment healer weight by 2 every 25 rounds until it reaches the max weight for healers
        if (gc.round() % 25 == 0) and MyVars.healerWeight < Constants.HEALER_MAX_WEIGHT:
            MyVars.healerWeight += 2
        # get current relevant information from all our units
        MyVars.workerCount = 0
        MyVars.rangerCount = 0
        MyVars.rocketCount = 0
        MyVars.factoryCount = 0
        MyVars.knightCount = 0
        MyVars.mageCount = 0
        MyVars.healerCount = 0
        Memory.current_vision_earth = {}
        for unit in gc.my_units():

            visionRange = 0
            RANGER_VISION = 70
            WKH_VISION = 50
            MAGE_VISION = 30

            if unit.unit_type == bc.UnitType.Worker:
                MyVars.workerCount += 1
                visionRange = Constants.WKH_VISION
            elif unit.unit_type == bc.UnitType.Ranger:
                MyVars.rangerCount += 1
                visionRange = Constants.RANGER_VISION
            elif unit.unit_type == bc.UnitType.Rocket:
                MyVars.rocketCount += 1
                visionRange = 2
            elif unit.unit_type == bc.UnitType.Factory:
                MyVars.factoryCount += 1
                visionRange = 2
            elif unit.unit_type == bc.UnitType.Mage:
                MyVars.mageCount += 1
                visionRange = Constants.MAGE_VISION
            elif unit.unit_type == bc.UnitType.Knight:
                MyVars.mageCount += 1
                visionRange = Constants.WKH_VISION
            elif unit.unit_type == bc.UnitType.Healer:
                MyVars.mageCount += 1
                visionRange = Constants.WKH_VISION

            if unit.location.is_on_map():

                if unit.location.map_location().planet == bc.Planet.Mars and gc.karbonite_at(unit.location.map_location()) > 0:
                    karboniteMapMars[
                        (unit.location.map_location().x, unit.location.map_location().y)] = gc.karbonite_at(
                        unit.location.map_location())

                seen_units = gc.sense_nearby_units(unit.location.map_location(), visionRange)
                for otherUnit in seen_units:
                    if otherUnit.team != my_team:
                        tempLoc = otherUnit.location.map_location()
                        asTuple = (tempLoc.x, tempLoc.y)
                        if unit.location.map_location().planet == bc.Planet.Earth:
                            if asTuple not in Memory.current_vision_earth:
                                Memory.current_vision_earth[asTuple] = otherUnit
                        else:
                            if asTuple not in Memory.current_vision_mars:
                                Memory.current_vision_mars[asTuple] = otherUnit

        if (gc.round() % 100 == 0):
            count = 0
            for key in karboniteMapEarth:
                count += karboniteMapEarth[key]

        if gc.round() > 25:
            Constants.HARVEST_AMOUNT = 4
        # walk through our units:
        # this code will primarily be used to determine
        for unit in gc.my_units():
            #if we're close to the flood send everyone to mars
            if gc.round() > 660:
                if unit.unit_type in Constants.DANGEROUS_ENEMIES or unit.unit_type == bc.UnitType.Healer:
                    if unit.id not in Memory.marsTroops:
                        Memory.marsTroops.append(unit.id)

            if unit.unit_type == bc.UnitType.Worker:
                location = unit.location
                if location.is_on_map():
                    if (len(gc.my_units()) > 64 and len(
                            gc.my_units()) % 9 == 0 and MyVars.marsWorkerCount * 11 < MyVars.workerCount and len(
                            Memory.marsTroops) * 2 < len(gc.my_units())):
                        if unit.id not in Memory.marsTroops:
                            Memory.marsTroops.append(unit.id)
                            MyVars.marsWorkerCount += 1

                    WorkerLogic(unit)
                    continue
            elif unit.unit_type == bc.UnitType.Ranger:
                location = unit.location
                if location.is_on_map():
                    if (len(gc.my_units()) > 64 and len(gc.my_units()) % 3 == 0 and (
                            MyVars.marsMageCount + MyVars.marsRangerCount) * 2 < (
                            MyVars.mageCount + MyVars.rangerCount) and len(Memory.marsTroops) * 2 < len(gc.my_units())):
                        if unit.id not in Memory.marsTroops:
                            Memory.marsTroops.append(unit.id)
                            MyVars.marsRangerCount += 1
                    ranger_logic(unit)
                    continue
            elif unit.unit_type == bc.UnitType.Mage:
                location = unit.location
                if location.is_on_map():
                    if (len(gc.my_units()) > 64 and len(gc.my_units()) % 3 == 0 and (
                            MyVars.marsMageCount + MyVars.marsRangerCount) * 2 < (
                            MyVars.mageCount + MyVars.rangerCount) and len(Memory.marsTroops) * 2 < len(gc.my_units())):
                        if unit.id not in Memory.marsTroops:
                            Memory.marsTroops.append(unit.id)
                            MyVars.marsMageCount += 1
                    mage_logic(unit)
                    continue
            elif unit.unit_type == bc.UnitType.Healer:
                location = unit.location
                if location.is_on_map():
                    if (len(gc.my_units()) > 64 and len(
                            gc.my_units()) % 7 == 0 and MyVars.marsHealerCount * 4 < MyVars.healerCount and len(
                            Memory.marsTroops) * 2 < len(gc.my_units())):
                        if unit.id not in Memory.marsTroops:
                            Memory.marsTroops.append(unit.id)
                            MyVars.marsHealerCount += 1
                    healer_logic(unit)
                    continue
            # utilities logic
            elif unit.unit_type == bc.UnitType.Factory:
                factory_logic(unit)
                continue
            elif unit.unit_type == bc.UnitType.Rocket:
                location = unit.location
                if unit.structure_is_built and location.is_on_map():
                    rocket_logic(unit)

    except Exception as e:
        print('Error:', e)
        # use this to show where the error was
        traceback.print_exc()

    
    # send the actions we've performed, and wait for our next turn.
    gc.next_turn()

    # these lines are not strictly necessary, but it helps make the logs make more sense.
    # it forces everything we've written this turn to be written to the manager.
    sys.stdout.flush()
    sys.stderr.flush()
