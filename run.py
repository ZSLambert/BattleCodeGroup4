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

class Constants:
    LAUNCH_BY = 749
    DESIRED_WORKERS = 10
    DESIRED_FACTORIES = 4
    DESIRED_ROCKETS = 4
    DIRECTION_CHANGES = [(0,1),(0,-1),(1,0),(-1,0),(1,1),(-1,-1),(1,-1),(-1,1)]
    REPLICATE_COST = 60
    WORKER_COST = 50
    OTHER_COST = 40
    ROCKET_COST = 150
    FACTORY_COST = 200
    HARVEST_AMOUNT = 3
    CHANGE_FROM_DIRECT = {
        bc.Direction.Center: (0,0),
        bc.Direction.South: (0,-1),
        bc.Direction.North: (0,1),
        bc.Direction.East: (1,0),
        bc.Direction.West: (-1,0),
        bc.Direction.Southeast: (1,-1),
        bc.Direction.Southwest: (-1,-1),
        bc.Direction.Northeast: (1,1),
        bc.Direction.Northwest: (-1,1)
    }
    DESTINATION_REACHED = [(-1000,-1000)]
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


class MyVars:
    workerCount = 0
    rangerCount = 0
    rocketCount = 0
    factoryCount = 0
    knightCount = 0
    mageCount = 0
    healerCount = 0
    rangerWeight = 0
    mageWeight = 0
    healerWeight = 10
    
    marsWorkerCount = 0
    marsRangerCount = 0
    marsMageCount = 0
    marsHealerCount = 0
    
    factoryLocations = []
    rocketLocations = []
    
    

print("pystarted")

# It's a good idea to try to keep your bots deterministic, to make debugging easier.
# determinism isn't required, but it means that the same things will happen in every thing you run,
# aside from turns taking slightly different amounts of time due to noise.
random.seed(6137)

my_team = gc.team()



#inverts a point on the map - used to estimate where the enemy will be
def invertPoint(point, planet):
    ptX = point[0]
    ptY = point[1]
    invertedX = earthMap.width - ptX - 1
    invertedY = earthMap.height - ptY - 1
    
    return (invertedX, invertedY)
    
#determines whether a map location is on the map based on its x and y coordinates  
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

#takes in a list of locations and finds the one "closest" to the destination based on a simple
#distance heuristic.  It also returns the index of the location it chose.
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

def evalFactorySpot(location):
    score = 100
    
    if (location.x, location.y) in karboniteMapEarth:
        score-=100
    
    for change in Constants.DIRECTION_CHANGES:
        newLoc = bc.MapLocation(location.planet, location.x + change[0], location.y + change[1])
        if onMap(newLoc):
            if not earthMap.is_passable_terrain_at(newLoc) or newLoc in MyVars.factoryLocations:
                score-=30
        else:
            score-=30
    return score
    

#takes in a unit and a maplocation of a destination, then will return whatever step needs to be taken
#to reach the destination quickest
#current pathfinding algorithm
def BFS_firstStep(unit, destination):
    global totalBFSTime
    global unreachableTime
    #get the position of the unit that we are trying to move.
        
    startT = int(round(time.time() * 1000))

    start = unit.location.map_location()
    
    startLoc = (start.x, start.y)
    destLoc = (destination.x, destination.y)
    
    ##print("Trying to get from " + str(startLoc) + " to " + str(destLoc))
    
    planet = start.planet
    
    parent = {}
    queue = [startLoc]
    visited = []
    while queue:
        #to intelligently choose nodes, get the one with the lowest straight line distance to destination, then remove that node from the queue.
        node, index = lowestDist(queue, destination)
        queue.pop(index)
        visited.append(node)
        if node == destLoc:
            #starts a list which will track the entire path from the end to the exit
            #ends up reversing it and returning the location of the first step
            path = [destLoc]
            while path[-1] != startLoc:
                path.append(parent[path[-1]])
            path.reverse()
            ##print("BFS took " + str(int(round(time.time() * 1000)) - startT) + " time.")
            totalBFSTime += int(round(time.time() *1000)) - startT
            #debugging in case we ever have the same destination as start point
            if len(path) == 1:
                #print(path)
                #print(startLoc)
                #print(destLoc)
                #print("Destination was the start point")
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
                parent[adjLoc] = node # <<<<< record the parent of the node - used to get the path
                queue.append(adjLoc)
        #current bugFix - hoping to remove in the future - handles cases where we are trying to reach an unreachable destination.
    unreachableTime += int(round(time.time() *1000)) - startT
    print(str(startLoc) + " trying to get to " + str(destLoc) + " was unreachable.")
    #print("Destination was unreachable")
    #print("Start: " + str(startLoc))
    #print("Destination: " + str(destLoc))
    return Constants.DESTINATION_REACHED

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


def mapReachable():
    for unit in gc.my_units():
        #make a coordinate from the location
        loc = unit.location.map_location().x, unit.location.map_location().y
        alreadySearched = False
        for cluster in Memory.reachable_clusters:
            if loc in cluster:
                placeholder = alreadySearched = True
        if not alreadySearched:
            newCluster = getReachable(unit)
            Memory.reachable_clusters.append(newCluster)
        
def getNeighbors(location):
    
    neighbors = []
    #goes through all the different changes that could be applied to a position, and adds them to our list if they have passable terrain
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

#find the closest location - based on simple heuristic - with karbonite to our initial location.
def nearbyKarb(location, planet):
    global totalNearbyKarbTime
    takenDest = []
    for key in Memory.worker_paths:
        
        takenDest.append(Memory.worker_paths[key][-1])
    startT = int(round(time.time() * 1000))
    
    
    locCluster = []
    for cluster in Memory.reachable_clusters:
        if (location.x, location.y) in cluster:
            locCluster = cluster    
    minDist = 100000
    minDistLoc = location
    for key in karboniteMapEarth:
        #print("Checking " + str(key))
        if key in takenDest or key not in locCluster:
            #we dont want to send two workers to the exact same place
            #we also dont want to bother returning a spot thats not reachable
            continue
        tempDist = pow(location.x - key[0], 2) + pow(location.y - key[1], 2)
        if tempDist < minDist:
            minDist = tempDist
            minDistLoc = bc.MapLocation(location.planet, key[0], key[1])
    
    totalNearbyKarbTime += int(round(time.time() *1000)) - startT
    return minDistLoc

#given a unit and a direction, returns the location of the unit moved in that direction.
def locFromDirect(unit, direction):
    location = unit.location.map_location()
    change = Constants.CHANGE_FROM_DIRECT[direction]
    return bc.MapLocation(location.planet, location.x + change[0], location.y + change[1])


def moveMarsUnit(unit):
    print("Moving Mars troop")
    curPlanet = unit.location.map_location().planet

    # print("Destination for me is " + str(Memory.rocket_destination[unit.id]))

    destination = bc.MapLocation(curPlanet, Memory.rocket_destination[unit.id].x,
                                 Memory.rocket_destination[unit.id].y)

    try:

        if not gc.is_occupiable(destination) or not earthMap.is_passable_terrain_at(destination):
            return
    except:
        placeholder = True

        # print(str(destination) + " was not on the map")
    # print(destination)

    try:
        # get the destination that this unit is supposed to be going to
        path = Memory.marsTroop_paths[unit.id]
        # if we already reached that destination: get a new one
        if path == Constants.DESTINATION_REACHED:
            placeholder = True
    except:
        # this will only happen the first time a destination is generated for a spot
        path = BFS_firstStep(unit, destination)

        Memory.marsTroop_paths[unit.id] = path

    # move in the correct direction to get to our destination if possible.

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
            # print("Movement is on cooldown - Troops for mars")
        else:
            for i in np.random.permutation(8):
                myDirection = directions[i]
                if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return 



def moveCombatUnit(unit):

    curPlanet = unit.location.map_location().planet

    destination = bc.MapLocation(curPlanet, Memory.combat_destinations[unit.id][0], Memory.combat_destinations[unit.id][1])
    try:
    
        if not earthMap.is_passable_terrain_at(destination):
            return
    except:
        placeholder = True
        #print(str(destination) + " was not on the map")
    
    try:
        #get the destination that this unit is supposed to be going to
        path = Memory.combat_paths[unit.id]
        #if we already reached that destination: get a new one
        if path == Constants.DESTINATION_REACHED:
            for i in np.random.permutation(8):
                myDirection = directions[i]
                if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return 
        
    except:
        #this will only happen the first time a destination is generated for a spot
        path = BFS_firstStep(unit, destination)
        
        #they only travel half way to the enemy start point
        n = math.floor(len(path)/2)
        del path[-n:]
        
        Memory.combat_paths[unit.id] = path

    #move in the correct direction to get to our destination if possible.
    nextStep = bc.MapLocation(unit.location.map_location().planet, path[0][0], path[0][1])


    myDirection = unit.location.map_location().direction_to(nextStep)

    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
        gc.move_robot(unit.id, myDirection)
        #remove the first step of the path that we had.

        Memory.combat_paths[unit.id] = path[1:]
        if (Memory.combat_paths[unit.id] == []):
            Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED
        return
    else:
        if not gc.is_move_ready(unit.id):
            placeholder = True
        else:
            #avoidObstacle(unit)
            print("Bad direction to move to - combat")
            for i in np.random.permutation(8):
                myDirection = directions[i]
                if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return 
    
def moveWorker(unit):
    
    try:
        #get the destination that this unit is supposed to be going to
        path = Memory.worker_paths[unit.id]
        #if we already reached that destination: get a new one
        if path == Constants.DESTINATION_REACHED:
            destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)
            path = BFS_firstStep(unit, destination)
            Memory.worker_paths[unit.id] = path
    except:
        #this will only happen the first time a destination is generated for a spot
        destination = nearbyKarb(unit.location.map_location(), bc.Planet.Earth)

        path = BFS_firstStep(unit, destination)

        Memory.worker_paths[unit.id] = path

    #move in the correct direction to get to our destination if possible.

    nextStep = bc.MapLocation(unit.location.map_location().planet, path[0][0], path[0][1])


    myDirection = unit.location.map_location().direction_to(nextStep)

    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
        gc.move_robot(unit.id, myDirection)
        #remove the first step of the path that we had.

        Memory.worker_paths[unit.id] = path[1:]
        if (Memory.worker_paths[unit.id] == []):
            Memory.worker_paths[unit.id] = Constants.DESTINATION_REACHED
        return
    else:
        if not gc.is_move_ready(unit.id):
            placeholder = True
            #print("Movement is on cooldown - worker")
        else:
            
            print("Bad direction to move to - worker")
            #avoidObstacle(unit)

            
def getAttackRange(unit):
    if unit.unit_type == bc.UnitType.Ranger:
        return Constants.RANGER_RANGE
    elif unit.unit_type == bc.UnitType.Mage:
        return Constants.MAGE_RANGE
    elif unit.unit_type == bc.UnitType.Knight:
        return Constants.KNIGHT_RANGE
    else:
        return 0
            
def inDanger(unit):
    
    ourLoc = unit.location.map_location()
    
    for key in Memory.current_vision_earth:
        enemyUnit = Memory.current_vision_earth[key]
        enemyLoc = enemyUnit.location.map_location()
        enemyRange = getAttackRange(enemyUnit)
        distTo = pow(enemyLoc.x - ourLoc.x, 2) + pow(enemyLoc.y - ourLoc.y, 2)
        if enemyUnit.unit_type == bc.UnitType.Ranger:
            if distTo > 10 and distTo <= enemyRange:
                return True
        else:
            if distTo <= enemyRange:
                return True
    return False
        
        
    
def tryToMoveToSafety(unit):
    toCheck = getNeighbors(unit.location.map_location())
    toCheck.append(unit.location.map_location())
    
    for spot in list(toCheck):
        if not gc.is_occupiable(spot) and spot != unit.location.map_location():
            toCheck.remove(spot)
    
    ourLoc = unit.location.map_location()

    damageDict = {}
    #initialize dictionary
    for spot in toCheck:
        damageDict[(spot.x,spot.y)] = 0

    
    for key in Memory.current_vision_earth:
        enemyUnit = Memory.current_vision_earth[key]
        enemyType = enemyUnit.unit_type
        if enemyType in Constants.DANGEROUS_ENEMIES:
            enemyRange = getAttackRange(enemyUnit)
            enemyLoc = enemyUnit.location.map_location()
            if pow(ourLoc.x - enemyLoc.x,2) + pow(ourLoc.y - enemyLoc.y,2) < 55:
                for spot in toCheck:
                    distTo = pow(spot.x - enemyLoc.x,2) + pow(spot.y - enemyLoc.y,2)
                    if enemyType == bc.UnitType.Ranger:
                        if distTo <= enemyRange and distTo > 10:
                            damageDict[(spot.x,spot.y)] += enemyUnit.damage()
                    else:
                        if distTo <= enemyRange:
                            damageDict[(spot.x,spot.y)] += enemyUnit.damage()
    #damageDict will now list the damage we will take at any one of these spots
    
    
    minDamage = 10000
    bestSpots = []
    print("Damage dict:")
    print(damageDict)
    for spot in toCheck:
        if damageDict[(spot.x,spot.y)] < minDamage:
            minDamage = damageDict[spot.x,spot.y]
            bestSpots = [spot]
        elif damageDict[spot.x,spot.y] == minDamage:
            bestSpots.append(spot)
    
    print("Min damage is " + str(minDamage))
    
    if minDamage > unit.health:
        print(str(minDamage) + " is > " + str(unit.health))
        #this means we die no matter where we move, so we might as well not try to.
        return False
    else:
        randNum = 0
        if len(bestSpots) > 1:
            randNum = random.randint(0, len(bestSpots)-1)
        
        chosenSpot = bestSpots[randNum]
        myDirection = unit.location.map_location().direction_to(chosenSpot)
        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
            gc.move_robot(unit.id, myDirection)
            if unit.unit_type == bc.UnitType.Worker:
                Memory.worker_paths[unit.id] = Constants.DESTINATION_REACHED
            else:
                Memory.combat_paths[unit.id] = Constants.DESTINATION_REACHED
            return True
        print("Couldn't move that direction")
        return False
        
        

def WorkerLogic(unit):
    ##priorities should be:
    # escape from enemies
    # replicate if we need more workers
    # harvest karbonite if near it / build structures if near it
    # move towards karbonite / nearest unbuilt structure
    
    #code to escape from enemies close
    
    if inDanger(unit):
        print("I'm in danger!")
        successful = tryToMoveToSafety(unit)
        if successful:
            print("Succesfully moved out of danger!")
            return
        
    if MyVars.rocketCount > 0 and unit.id in Memory.marsTroops and unit.location.map_location().planet == bc.Planet.Earth:
        if unit.id not in Memory.rocket_destination:
            rocketFound = False
            nearby = gc.sense_nearby_units(location.map_location(), Constants.WKH_VISION)
            for place in nearby:
                # print(place)
                if place.team == my_team and place.unit_type == bc.UnitType.Rocket:
                    rocketFound = True
                    Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,
                                                                        place.location.map_location().x + 1,
                                                                        place.location.map_location().y)

            if not rocketFound:
                randNum = random.randint(0, len(MyVars.rocketLocations) - 1)
                Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth, MyVars.rocketLocations[
                    randNum].x + 1, MyVars.rocketLocations[randNum].y)

        moveMarsUnit(unit)
        return
    #if we have reached our destination, change this units destination to a placeholder representing
    #that it has been reached.
    try:
        if unit.location.map_location() == Memory.worker_paths[unit.id]:
            Memory.worker_paths[unit.id] = Constants.DESTINATION_REACHED
    except:
        #do nothing - here so that we don't get an error if we haven't calculated a path yet
        placeHolder = True
    
    #if we don't have enough workers, 
    if MyVars.workerCount < Constants.DESIRED_WORKERS and gc.karbonite() >= Constants.REPLICATE_COST:
        direct = getNeighbors(unit.location.map_location())
        for i in range(len(direct)):
            direction = unit.location.map_location().direction_to(direct[i])
            if gc.can_replicate(unit.id, direction):
                gc.replicate(unit.id, direction)
                MyVars.workerCount += 1
    else:
        #get locations which are passable nearby
        validLocs = getNeighbors(unit.location.map_location())
        
        #get nearby units and build them if possible
        nearby = gc.sense_nearby_units(unit.location.map_location(), 2)
        for tempUnit in nearby:
            if gc.can_build(unit.id, tempUnit.id):
                #print("Building!")
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
        
        #try to build a factory blueprint if we don't have enough and have sufficient karbonite
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
        
        #if we're close enough to our destination, harvest any karbonite that is near us
        distToDest = 0
        try:
            if Memory.worker_paths[unit.id] == Constants.DESTINATION_REACHED:
                distToDest = 0
            else:
                tempDest = Memory.worker_paths[unit.id][-1]
                distToDest = pow(tempDest[0] - unit.location.map_location().x, 2) + pow(tempDest[1] - unit.location.map_location().y, 2)
        except:
            distToDest = 0
        if distToDest < 5:
            
            for direct in directions:
                if gc.can_harvest(unit.id, direct):
                    gc.harvest(unit.id, direct)
                    harvestedLoc = locFromDirect(unit, direct)

                    #if this one is here harvesting, then make sure that other ones go somewhere else
                    for key in Memory.worker_paths:
                        if (harvestedLoc.x, harvestedLoc.y) == Memory.worker_paths[key][-1]:
                            Memory.worker_paths[key] = Constants.DESTINATION_REACHED

                    if unit.location.map_location().planet == bc.Planet.Earth:

                        if (gc.karbonite_at(harvestedLoc) < 1):
                            del karboniteMapEarth[(harvestedLoc.x,harvestedLoc.y)]
                        else:
                            karboniteMapEarth[(harvestedLoc.x,harvestedLoc.y)] = gc.karbonite_at(harvestedLoc)
                        #print("After harvesting there is now " + str(karboniteMapEarth[harvestedLoc.x][harvestedLoc.y]))
                    else:
                        karboniteMapMars[harvestedLoc.x][harvestedLoc.y] = gc.karbonite_at(harvestedLoc)
                    return
        
        
        if len(karboniteMapEarth) > 0:
            moveWorker(unit)
        
        else:
            for i in np.random.permutation(8):
                myDirection = directions[i]
                if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
                    gc.move_robot(unit.id, myDirection)
                    return 

            
            

def karbMultiplier(location):
    minDistEnemy = 1000000
    minDistFriendly = 1000000
    
    for spot in Constants.START_POINTS:
        tempDist = math.sqrt(pow(location.x - spot[0],2) + pow(location.x - spot[1],2))
        if tempDist < minDistFriendly:
            minDistFriendly = tempDist
    
    for spot in Constants.ENEMY_START_POINTS:
        tempDist = math.sqrt(pow(location.x - spot[0],2) + pow(location.x - spot[1],2))
        if tempDist < minDistEnemy:
            minDistEnemy = tempDist
    
    if minDistFriendly >= minDistEnemy * 2:
        return 0
    
    reachable = False
    for cluster in Memory.reachable_clusters:
        if (location.x, location.y) in cluster:
            reachable = True
    
    if reachable:
        return 1
    else:
        return 0

    
def rocket_logic(unit):
    garrison = unit.structure_garrison()
    if unit.location.map_location().planet == bc.Planet.Earth:
        destination = bc.MapLocation(bc.Planet.Mars, unit.location.map_location().x, unit.location.map_location().y)
        if inDanger(unit) and len(garrison) > 0:
            if gc.can_launch_rocket(unit.id, destination):
                gc.launch_rocket(unit.id, destination)
                MyVars.rocketLocations.remove(unit.location.map_location)
                MyVars.rocketCount -= 1
                print("Performed a panic rocket launch")
        elif len(garrison) < 8:
            nearby = gc.sense_nearby_units(location.map_location(), Constants.ROCKET_VISION)
            for place in nearby:
                if place.team == my_team and gc.can_load(unit.id, place.id):
                    gc.load(unit.id, place.id)
        elif gc.can_launch_rocket(unit.id, destination):
            gc.launch_rocket(unit.id, destination)
            MyVars.rocketLocations.remove(unit.location.map_location)
            MyVars.rocketCount -= 1
    elif unit.location.map_location().planet == bc.Planet.Mars:
        if len(garrison) > 0:
            d = random.choice(directions)
            if gc.can_unload(unit.id, d):
                print('unloaded a unit on mars!')
                gc.unload(unit.id, d)
        else:
            gc.disintegrate_unit(unit.id)    
    


def ranger_logic(unit):        
    
    if unit.id in Memory.marsTroops and unit.location.map_location().planet == bc.Planet.Earth and MyVars.rocketCount > 0:
        if unit.id not in Memory.rocket_destination:
            rocketFound = False
            nearby = gc.sense_nearby_units(location.map_location(), Constants.HEALER_VISION)
            for place in nearby:
                # print(place)
                if place.team == my_team and place.unit_type == bc.UnitType.Rocket:
                    rocketFound = True
                    Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,place.location.map_location().x + 1,place.location.map_location().y)

            if not rocketFound:
                randNum = random.randint(0, len(MyVars.rocketLocations) - 1)
                Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth, MyVars.rocketLocations[randNum].x + 1, MyVars.rocketLocations[randNum].y)

        moveMarsUnit(unit)
        return
    
    if unit.id not in Memory.combat_destinations:
        randNum = random.randint(0,len(Constants.ENEMY_START_POINTS)-1)
        #print("We'll be going towards the " + str(randNum) + " starting point.")
        Memory.combat_destinations[unit.id] = Constants.ENEMY_START_POINTS[randNum]
    
    if inDanger(unit):
        print("I'm in danger!")
        successful = tryToMoveToSafety(unit)
        if successful:
            print("Succesfully moved out of danger!")
    
    nearby= gc.sense_nearby_units(location.map_location(), Constants.RANGER_VISION)
    for place in nearby:
        if place.team != my_team and gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, place.id):
            #print("Ranger attacked a unit!")
            gc.attack(unit.id, place.id)
            return
    #commented out since this is broken right now
    #for place in nearby:
    #    if place.team != my_team and not gc.can_attack(unit.id, place.id):
    #        myDirection = BFS_firstStep(unit, place.location.map_location())[-1]
    #        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
    #            gc.move_robot(unit.id, myDirection)
    #            continue
    moveCombatUnit(unit)

        
def mage_logic(unit):
    
    if unit.id in Memory.marsTroops and unit.location.map_location().planet == bc.Planet.Earth and MyVars.rocketCount > 0:
        if unit.id not in Memory.rocket_destination:
            rocketFound = False
            nearby = gc.sense_nearby_units(location.map_location(), Constants.HEALER_VISION)
            for place in nearby:
                # print(place)
                if place.team == my_team and place.unit_type == bc.UnitType.Rocket:
                    rocketFound = True
                    Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,place.location.map_location().x + 1,place.location.map_location().y)

            if not rocketFound:
                randNum = random.randint(0, len(MyVars.rocketLocations) - 1)
                Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth, MyVars.rocketLocations[randNum].x + 1, MyVars.rocketLocations[randNum].y)

        moveMarsUnit(unit)
        return
    
    
    if unit.id not in Memory.combat_destinations:
        randNum = random.randint(0,len(Constants.ENEMY_START_POINTS)-1)
        Memory.combat_destinations[unit.id] = Constants.ENEMY_START_POINTS[randNum]
    
    
    if inDanger(unit):
        print("I'm in danger!")
        successful = tryToMoveToSafety(unit)
        if successful:
            print("Succesfully moved out of danger!")
    #same as ranger logic but for the mages
    nearby= gc.sense_nearby_units(location.map_location(), Constants.MAGE_VISION)
    for place in nearby:
        if place.team != my_team and gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, place.id):
            #print("Mage attacked a unit!")
            gc.attack(unit.id, place.id)
            continue
    #commented out since this is broken right now
    #for place in nearby:
    #    if place.team != my_team and not gc.can_attack(unit.id, place.id):
    #        myDirection = BFS_firstStep(unit, place.location.map_location())[-1]
    #        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
    #            gc.move_robot(unit.id, myDirection)
    #            continue
    moveCombatUnit(unit)



def healer_logic(unit):
    #same as ranger logic but for the Healer. the healer attacks our teams units to heal them.
    
    if unit.id in Memory.marsTroops and unit.location.map_location().planet == bc.Planet.Earth and MyVars.rocketCount > 0:
        if unit.id not in Memory.rocket_destination:
            rocketFound = False
            nearby = gc.sense_nearby_units(location.map_location(), Constants.HEALER_VISION)
            for place in nearby:
                # print(place)
                if place.team == my_team and place.unit_type == bc.UnitType.Rocket:
                    rocketFound = True
                    Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth,place.location.map_location().x + 1,place.location.map_location().y)

            if not rocketFound:
                randNum = random.randint(0, len(MyVars.rocketLocations) - 1)
                Memory.rocket_destination[unit.id] = bc.MapLocation(bc.Planet.Earth, MyVars.rocketLocations[randNum].x + 1, MyVars.rocketLocations[randNum].y)

        moveMarsUnit(unit)
        return
    
    
    if inDanger(unit):
        print("I'm in danger!")
        successful = tryToMoveToSafety(unit)
        if successful:
            print("Succesfully moved out of danger!")
    
    nearby= gc.sense_nearby_units(location.map_location(), Constants.HEALER_VISION)
    for place in nearby:
        if place.team == my_team and gc.is_attack_ready(unit.id) and gc.can_attack(unit.id, place.id):
            #print("Healed a unit!")
            gc.attack(unit.id, place.id)
            continue
    #commented out since this is broken right now
    #for place in nearby:
    #    if place.team != my_team and not gc.can_attack(unit.id, place.id):
    #        myDirection = BFS_firstStep(unit, place.location.map_location())[-1]
    #        if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
    #            gc.move_robot(unit.id, myDirection)
    #            continue
    myDirection = directions[random.randint(0,7)]
    if gc.can_move(unit.id, myDirection) and gc.is_move_ready(unit.id):
        gc.move_robot(unit.id, myDirection)       

def factory_logic(unit):
    garrison = unit.structure_garrison()
    if len(garrison) > 0:
        d = random.choice(directions)
        if gc.can_unload(unit.id, d):
            gc.unload(unit.id, d)
            return
    elif gc.can_produce_robot(unit.id, bc.UnitType.Ranger):
        toproduce = random.randint(0,(MyVars.mageWeight + MyVars.rangerWeight+ MyVars.healerWeight))
        if toproduce <= MyVars.rangerWeight:
            gc.produce_robot(unit.id, bc.UnitType.Ranger)
            return
        elif toproduce <= (MyVars.mageWeight + MyVars.rangerWeight):
            gc.produce_robot(unit.id, bc.UnitType.Mage)
            return
        elif toproduce <= (MyVars.mageWeight + MyVars.rangerWeight+ MyVars.healerWeight):
            gc.produce_robot(unit.id, bc.UnitType.Healer)
            return        

###INITIAL SETUP###


#get initial variables and maps

gc.queue_research(bc.UnitType.Worker)
gc.queue_research(bc.UnitType.Rocket)
gc.queue_research(bc.UnitType.Mage)
gc.queue_research(bc.UnitType.Ranger)
gc.queue_research(bc.UnitType.Mage)
gc.queue_research(bc.UnitType.Mage)


directions = list(bc.Direction)

earthMap = gc.starting_map(bc.Planet.Earth)
marsMap = gc.starting_map(bc.Planet.Mars)

earthWidth = earthMap.width
earthHeight = earthMap.height

print("Earth is " + str(earthWidth) + "x" + str(earthHeight))

if earthWidth >= 35 and earthHeight >= 35:
    MyVars.rangerWeight = 45
    MyVars.mageWeight = 30
else:
    MyVars.rangerWeight = 30
    MyVars.mageWeight = 45

marsWidth = marsMap.width
marsHeight = marsMap.height

#create maps of what places are passable and what places have karbonite on them
karboniteMapEarth = {}
karboniteMapMars = {}
passableMapEarth = []
passableMapMars = []

#create the shells of the maps
for i in range(earthWidth):
    passableMapEarth.append([False] * earthHeight)


for i in range(marsWidth):
    passableMapMars.append([False] * marsHeight)

totalCount = 0

mapReachable()

#get all of our starting points as well as the likely enemy starting points


for unit in gc.my_units():
    loc = unit.location.map_location()
    temp = (loc.x, loc.y)
    Constants.START_POINTS.append(temp)

for point in Constants.START_POINTS:
    Constants.ENEMY_START_POINTS.append(invertPoint(point, bc.Planet.Earth))        

#add in numbers/booleans for where karbonite/passable terrain is.
for i in range(earthWidth):
    for j in range(earthHeight):
        #print("Working with point " + str(i) + "," + str(j))
        loc = bc.MapLocation(bc.Planet.Earth, i, j)
        karbCount = int(earthMap.initial_karbonite_at(loc)) * karbMultiplier(loc)
        if(karbCount > 0):
            totalCount+=karbCount
            karboniteMapEarth[(i,j)] = int(earthMap.initial_karbonite_at(loc))
        passableMapEarth[i][j] = earthMap.is_passable_terrain_at(loc)
        #print(str(i) + "," + str(j) + " is passable is " + str(earthMap.is_passable_terrain_at(loc)))

print(karboniteMapEarth)        

for i in range(marsWidth):
    for j in range(marsHeight):
        loc = bc.MapLocation(bc.Planet.Mars, i, j)
        karbCount = int(marsMap.initial_karbonite_at(loc))
        if(karbCount > 0):
            karboniteMapMars[(i,j)] = int(marsMap.initial_karbonite_at(loc))
        passableMapMars[i][j] = marsMap.is_passable_terrain_at(loc)
        
#now, on earth, try to scale the amount of karbonite so that places close to the enemy aren't listed as
#having any.  Also, remove any places that are unreachable by our people.



Constants.INITIAL_KARB_COUNT = totalCount        

for cluster in Memory.reachable_clusters:
    print(len(cluster))
        
while True:
    # We only support Python 3, which means brackets around print()
    print('pyround:', gc.round(), 'time left:', gc.get_time_left_ms(), 'ms')
    # frequent try/catches are a good idea
    try:
        #get current relevant information from all our units
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

        
        #print(Memory.current_vision_earth)
        #print("Combat paths are:")
        #print(Memory.combat_paths)
        if(gc.round() % 100 == 0):
            #print("Current karbonite map is:")
            count = 0
            for key in karboniteMapEarth:
                count+=karboniteMapEarth[key]
            print("There is " + str(count) + " karbonite remaining")
            
            #print(Memory.worker_paths)
            #print(Memory.combat_paths)
        if gc.round() > 25:
            Constants.HARVEST_AMOUNT = 4
        # walk through our units:
        #this code will primarily be used to determine 
        #print("we have " + str(len(gc.my_units())) + " units.")
        for unit in gc.my_units():
            if unit.unit_type == bc.UnitType.Worker:
                location = unit.location
                if location.is_on_map():
                    if (len(gc.my_units()) > 64 and len(gc.my_units()) % 9 == 0 and MyVars.marsWorkerCount * 11 < MyVars.workerCount and len(Memory.marsTroops) * 2 < len(gc.my_units())):
                        if unit.id not in Memory.marsTroops:
                            Memory.marsTroops.append(unit.id)
                            MyVars.marsWorkerCount += 1

                    WorkerLogic(unit)
                    continue
            elif unit.unit_type == bc.UnitType.Ranger:
                location = unit.location
                if location.is_on_map():
                    if (len(gc.my_units()) > 64 and len(gc.my_units()) % 3 == 0 and (MyVars.marsMageCount + MyVars.marsRangerCount) * 2 < (MyVars.mageCount + MyVars.rangerCount) and len(Memory.marsTroops) * 2 < len(gc.my_units())):
                        if unit.id not in Memory.marsTroops:
                            Memory.marsTroops.append(unit.id)
                            MyVars.marsRangerCount += 1
                    ranger_logic(unit)
                    continue
            elif unit.unit_type == bc.UnitType.Mage:
                location = unit.location
                if location.is_on_map():
                    if (len(gc.my_units()) > 64 and len(gc.my_units()) % 3 == 0 and (MyVars.marsMageCount + MyVars.marsRangerCount) * 2 < ( MyVars.mageCount + MyVars.rangerCount) and len(Memory.marsTroops) * 2 < len(gc.my_units())):
                        if unit.id not in Memory.marsTroops:
                            Memory.marsTroops.append(unit.id)
                            MyVars.marsMageCount += 1
                    mage_logic(unit)
                    continue
            elif unit.unit_type == bc.UnitType.Healer:
                location = unit.location
                if location.is_on_map():
                    if (len(gc.my_units()) > 64 and len(gc.my_units()) % 7 == 0 and MyVars.marsHealerCount * 4 < MyVars.healerCount and len(Memory.marsTroops) * 2 < len(gc.my_units())):
                        if unit.id not in Memory.marsTroops:
                            Memory.marsTroops.append(unit.id)
                            MyVars.marsHealerCount += 1
                    healer_logic(unit)
                    continue
            #utilities logic
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

    print("Nearby Karb took + " + str(totalNearbyKarbTime))
    print("BFS took + " + str(totalBFSTime))    
    print("Unreachable BFS took + " + str(unreachableTime))    
    #print("Avoidance took + " + str(avoidanceTime))    
    #print(str(successCount) + " successful avoidances of obstacles.")

    # send the actions we've performed, and wait for our next turn.
    gc.next_turn()

    # these lines are not strictly necessary, but it helps make the logs make more sense.
    # it forces everything we've written this turn to be written to the manager.
    sys.stdout.flush()
    sys.stderr.flush()

