# Pentago

![image](https://user-images.githubusercontent.com/90510471/178991969-a03441f7-8d39-4760-8ffe-bc84a1db9f4f.png)


This is the <strong>Final Submission</strong> README file for the <span style="color:red">Pentago Game Project.</span>

In this final state, the project has a fully functional board, game logic, and networking.

<u>The Java version used is JAVA 11.</u>

<strong>INSTRUCTIONS</strong>

<i>Local game</i>
* To start a local game (without server/client), run the Pentago class (preferably with arguments [name1, name2]). If
you prefer to run it without arguments, you can input the names when prompted. Depending on how you want to play, you
are free to choose between a Player vs Player, AI vs AI or Player vs AI game. If you want to play against an AI, input
<strong>(-easy)</strong> as one/both of the names.
* To make a move, type a number first in the range of (0 - 35) which represents a field on the board (visible in the
numbering shown alongside the board). Afterwards, you are prompted to input a rotation which is of the form (<strong>
"1+" - first quadrant clockwise</strong>). This applies to every quadrant by just changing the number (1-4), and the
sign after it (+ for clockwise, - for counterclockwise). This will repeat until the game has a winner.

<i>Multiplayer game</i>

* To start a server, run the ServerMain class found in the multiplayer.Server package. You will be prompted
to input an IP address. (<strong> keep in mind that the default port is <i>6969</I></strong> )
* In case you want to join your / another server, start a client by running the ClassMain class inside the
multiplayer.Client package. You will be prompted to input a valid IP address, a port, client type and a username.
* The AI clients are coded to automatically start queueing games infinitely, until asked to stop. The Human client
is fully manual and players can join servers without automatically being queued into a game.

<strong>NOTES</strong>


* Details on how to play the game or about the implementation can be found in our pdf report attached in the root
directory.

<strong>Hope that you enjoy our game and code! <span style="color:red">Have a wonderful day :) </span> </strong>


