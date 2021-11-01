%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 1. TYPE HIERARCHY

% Device is a type.

% A computer is a device.
device(D):- computer(D).

% A router is a device.
device(D):- router(D).

% A modem is a device.
device(D):- modem(D).


% A router is a sink device.
sinkDevice(D):- router(D).

% A computer is a sink device.
sinkDevice(D):- computer(D).

% A router is a source device.
sourceDevice(D):- router(D).

% A modem is a source device.
sourceDevice(D):- modem(D). 

deviceType(modem;router;computer).

deviceType(D,modem):- modem(D).
deviceType(D,router):- router(D).
deviceType(D,computer):- computer(D).


time(0..6).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 2. LOGIC OF NORMAL DEVICE BEHAVIOR

% A sink device is online if 
%   it is connected to source device
%   and the source device is online
% unless
%   the sink device is malfunctioning, or
%   the source device is malfunctioning.

holds(online(D),T):-
  sinkDevice(D),sourceDevice(D2),time(T),
  connected(D,D2),
  holds(online(D2),T),
  not holds(malfunctioning(D),T),
  not holds(malfunctioning(D2),T).
  

% A modem is online unless it is deactivated. 
holds(online(D),T):-
  modem(D),time(T),
  not holds(deactivated(D),T).
  
  


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 3. FAULTS AND THEIR PROBABILITIES


% A device may be initially malfunctioning at random.
{holds(malfunctioning(D),0)}:- device(D). 
randProp(holds(malfunctioning(D),0)):- device(D).


% A modem may initially be deactivated at random. 
{holds(deactivated(D),0)}:- modem(D).
randProp(holds(deactivated(D),0)):- modem(D).


%inertia (in HLL the compiler generates this.)

inertialFluent(deactivated(D)):- modem(D).
inertialFluent(malfunctioning(D)):- device(D).

holds(F,T):- 
  time(T), T>0, inertialFluent(F),
  holds(F,T-1),
  not holds(-F,T).
  
holds(-F,T):-
  time(T), T>0, inertialFluent(F),
  holds(-F,T-1),
  not holds(F,T).


% THe probability that a computer is initially malfunctioning is 2^-10.
cost(holds(malfunctioning(D),0),10):- computer(D), holds(malfunctioning(D),0).

% The probability that a router is initially malfunctioning is 2^-11.
cost(holds(malfunctioning(D),0),11):- router(D),holds(malfunctioning(D),0).

% The probability that a modem is initially malfunctioning is 2^-12.
cost(holds(malfunctioning(D),0),12):- modem(D), holds(malfunctioning(D),0).


% The probability that a modem is initially deactivated is 2^-9.
cost(holds(deactivated(D),0),9):- modem(D), holds(deactivated(D),0).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% 
% 4. PROBABILISTIC MODEL FOR  DEVICE CONFIGURATION

% The device indices are 1,..,50.  
deviceIndex(1..10).

% A device index *may* (or may not) be the name of computer, router,
% or modem.  These are random propositions.
{computer(D)}:- deviceIndex(D).
{router(D)}:- deviceIndex(D).
{modem(D)}:- deviceIndex(D). 
randProp(router(D)):- deviceIndex(D).
randProp(modem(D)):- deviceIndex(D).
randProp(computer(D)):-  deviceIndex(D).

% A device can only be of one most specific type.
:- computer(D), router(D).
:- router(D), modem(D).
:- modem(D), computer(D).

% A computer is most likely connected to a router, but may be
% connected to a modem. 
cost(router(D),3):- deviceIndex(D), D>1, computer(D-1),router(D).
cost(modem(D),10):- deviceIndex(D), D>1, computer(D-1), modem(D).

% A router is most likely connected to a modem, but may be 
% connected to another router. 
cost(modem(D),2):- deviceIndex(D), D>1, router(D-1),modem(D).
cost(router(D),12):- deviceIndex(D), D>1, router(D-1),router(D).

% Nothing is downstream of a modem.
:- modem(D), deviceIndex(D2), D2>D, device(D2).

% Each device is connected to the next device in the chain 
connected(D,D+1):- deviceIndex(D), device(D), device(D+1).




%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% 5. DIALOG STEPS: 


%  At most 1 dialog step may occur in a time step until the goal is achieved.
{do(A,T): time(T),dialogStep(A),possible(A,T)}.
:- time(T), dialogStep(A1), dialogStep(A2), A1 != A2, do(A1,T), do(A2,T).
:- do(A,T), dialogStep(A), time(T), goal(T). 


% There are three sorts of dialog steps in this model: getNextDevice,
% repair(D) where D is a device, and resetModem(M) where M is a modem.
% Each is described below in terms of its preconditions and effects. 

%%%%%%
% getNextDevice
% getNextDevice means ask what (kind of device) the most recently learned 
% device is connected to.
dialogStep(getNextDevice).

% We can ask for the next device at any time (but the system
% knows better to do this if the last found device is a modem).
possible(getNextDevice,T):- time(T).

% The number of known devices goes up if we ask the user for 
% the next device in the chain.
holds(numKnownDevices(D),T):-
  time(T), T>0, deviceIndex(D), 
  holds(numKnownDevices(D-1),T-1),
  do(getNextDevice,T-1).
  
% The number of known devices stays the same if we do not
% ask for another device.
holds(numKnownDevices(D),T):- 
  time(T), T>0, deviceIndex(D),
  holds(numKnownDevices(D),T-1),
  not do(getNextDevice,T-1).
  
% Devices are known if they are downstream of the most recently
% learned device. This is somewhat kludgy and could be done more
% elegantly. 
holds(knownDevice(D),T):- device(D), holds(numKnownDevices(N),T), D <= N.

%%%%%%
% repair(D)
% The dialog step repair(D) means suggest repairing device D and
% ask if it fixes the problem. 
dialogStep(repair(D,Ty)):- device(D),deviceType(D,Ty).

% repair(D) is possible if device D is known.
possible(repair(D,Ty),T):- time(T),device(D),deviceType(Ty), holds(knownDevice(D),T).

% repairing a device fixes a malfunction
holds(-malfunctioning(D),T):-
  time(T), T>0, device(D),deviceType(Ty),
  do(repair(D,Ty),T-1). 
  
%%%%%%
% resetModem(M) 
% Dialog step reset(M) means suggest resetting modem M and ask if
% that solved the problem. 
dialogStep(resetModem(M)):- modem(M). 

% Resetting M is possible if M is a modem and is a known device. 
possible(resetModem(D),T):- time(T), modem(D), holds(knownDevice(D),T).

% If a modem is deactivated, resetting it fixes the problem.
holds(-deactivated(D),T):-
  time(T), T>0, modem(D),
  do(resetModem(D),T-1).
  



%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CONSTRAINTS, REQUIREMENTS, AND OPTIMAL ANSWER SETS

% hard constraint: only consider answer sets that achieve the goal.
goal:- goal(T), time(T).
:- not goal.

% First priority: minimize the cost of the hypotheses (about the 
% unknown user configuration, jointly with the occurring faults)
#minimize {C@2,P: randProp(P), cost(P,C)}.

% Second priority: minimize the length of the plan required to
% achieve the goal.
#minimize {1@1,T : time(T), not goal(T)}.



%%%%%%%%%%%%%%%%%%%
% Test case data

% Initially, we only know the problem device, which is a computer
holds(numKnownDevices(1),0).
computer(1).

% The computer is initially not online
:-  holds(online(1),0).


% The goal is to get the problem device, device #1, online
goal(T):- holds(online(1),T),time(T).


 

#show computer/1.
#show router/1.
#show modem/1.
#show holds/2.
#show do/2.
#show goal/1.
#show deviceType/2.











