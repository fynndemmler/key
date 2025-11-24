//import java.util.UUID;
import java.util.List;
import java.util.*;

enum Coin {
    HEADS,
    TAILS
}

enum State {
    IDLE,
    GAME_AVAILABLE,
    BET_PLACED
}

enum Methods {
    TRANSFER,
    REMOVE_FROM_POT,
    CREATE_GAME,
    PLACE_BET,
    DECIDE_BET
}

class Address {
    int id;
    int balance;

    /*@ public normal_behavior
      @ requires id > 0 & balance > 0;
      @ ensures this.id == id & this.balance == balance;
     */
    public Address(int id, int balance) {
        this.id = id;
        this.balance = balance;
    }
}

/*
    Note that a falsey return value for any method in this class reflects aborted execution.
 */
class Casino {
    public Address operator;
    public Address player;
    public Coin guess;
    private /*@spec_public*/ Coin secret;
    public int pot;
    public int hashedNumber;
    public int bet;
    private State state;
    public Address sender;

    private /*@spec_public*/ boolean cond1;
    private /*@spec_public*/ boolean cond2;

    //@ invariant State.BET_PLACED != null && state.GAME_AVAILABLE != null && state.IDLE != null && Coin.HEADS != null && Coin.TAILS != null;

    // Proven
    /*@ public normal_behavior
      @ requires operator != null && player != null;
      @ ensures this.operator == operator && this.player == player && this.state == State.IDLE && this.pot == 0 && this.bet == 0 && this.hashedNumber == -1;
      @*/
    public void setupNewGame(Address operator, Address player) {
        this.operator = operator;
        this.player = player;
        this.state = State.IDLE;
        this.pot = 0;
        this.bet = 0;
        this.hashedNumber = -1;
    }

    /*@ public normal_behavior
      @ requires bet > 0 && amount > 0 && guess != null;
      @ requires operator != null && player != null && player != operator;
      @ ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_placeBet_int_Coin, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_removeFromPot_int, TRUE))\then(TRUE)\else(FALSE))))*);
      @ assignable \everything;
      @*/
    public void ESV_start1(int bet, int amount, Coin guess) {
        placeBet(bet, guess);
        removeFromPot(amount);
    }

    /*@ public normal_behavior
      @ requires bet > 0 && amount > 0 && guess != null;
      @ requires operator != null && player != null && player != operator;
      @ ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_placeBet_int_Coin, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_removeFromPot_int, TRUE))\then(TRUE)\else(FALSE))))*);
      @ assignable \everything;
      @*/
    public void SAFE_start1(int bet, int amount, Coin guess) {
        removeFromPot(amount);
        placeBet(bet, guess);
    }

    //eventSeq(event(decideBet, state == State.BET\_PLACED \&\& sender == operator \&\& hashedNumber == secretNumber, event(createGame, bet > 0))
    /*@ public normal_behavior
      @ requires hashedNumber > 0 && bet > 0;
      @ requires operator != null && player != null && player != operator;
      @ ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_decideBet_int, self.cond1))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_createGame_int, self.cond2))\then(TRUE)\else(FALSE))))*);
      @ assignable \everything;
      @*/
    public void ESV_start2(int secretNumber, int hashedNumber) {
        this.hashedNumber = hashedNumber;
        this.state = State.BET_PLACED;
        this.sender = this.operator;
        secretNumber = hashedNumber;
        cond1 = state == State.BET_PLACED && sender == operator && hashedNumber == secretNumber;
        decideBet(secretNumber);
        bet = 10;
        cond2 = bet > 0;
        createGame(hashedNumber);
    }

    /*@ public normal_behavior
      @ requires hashedNumber > 10 && bet > 0;
      @ requires operator != null && player != null && player != operator;
      @ ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_decideBet_int, self.cond1))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_createGame_int, self.cond2))\then(TRUE)\else(FALSE))))*);
      @ assignable \everything;
      @*/
    public void SAFE_start2(int secretNumber, int hashedNumber) {
        this.hashedNumber = hashedNumber;
        this.state = State.BET_PLACED;
        this.sender = this.operator;
        secretNumber = hashedNumber;
        cond1 = state == State.BET_PLACED && sender == operator && hashedNumber == secretNumber;
        decideBet(secretNumber);
        bet = 0;
        cond2 = bet > 0;
        createGame(hashedNumber);
    }

    // ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_removeFromPot_Address_int, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_placeBet_Address_int_Coin, TRUE))\then(TRUE)\else(FALSE))))*); // Works: Can be verified
    // ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_placeBet_Address_int_Coin, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_removeFromPot_Address_int, TRUE))\then(TRUE)\else(FALSE))))*); // Works: Can not be verfied
    // ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_placeBet_Address_int_Coin, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_removeFromPot_Address_int, TRUE))\then(TRUE)\else(FALSE))))*); // Works: Can not be verfied
    // ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_placeBet_Address_int_Coin, TRUE))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_removeFromPot_Address_int, TRUE))\then(TRUE)\else(FALSE))))*); // Works: Can not be verfied
    /*@ public normal_behavior
      @ requires operator != null && player != null && money > 0 && player != operator;
      @ ensures (*!eventSeq(seqConcat(seqSingleton(\if(event(Casino_decideBet_int, self.cond1))\then(TRUE)\else(FALSE)), seqSingleton(\if(event(Casino_createGame_int, self.cond2))\then(TRUE)\else(FALSE))))*);
      @ assignable \everything;
      @*/
    public boolean triggerSecondEventSequence(Address operator, Address player, int money, Coin guess) {
        setupNewGame(operator, player);
        state = State.BET_PLACED;
        sender = operator;
        hashedNumber = 1;
        int secretNumber = 1;
        bet = 10;
        cond1 = state == State.BET_PLACED && sender == operator && hashedNumber == secretNumber;
        decideBet(secretNumber);
        cond2 = bet < 0;
        createGame(10);
        return true;
    }

    // Proven
    /*
       Transfer money from an address. The money is just added to the pot and this abstract method
       simply reflects the transfer call from the original Casino contract. It has no effect on
       verification.
     */
    /*@ public normal_behavior
      @ requires transferee != null && amount > 0;
      @ ensures \result == true && transferee.balance == \old(transferee.balance) + amount;
      @ assignable transferee.balance;
      @*/
    public boolean transfer(Address transferee, int amount) {
        transferee.balance = transferee.balance + amount;
        return true;
    }

    /*@ public normal_behavior
      @ requires sender != null && amount > 0;
      @ ensures \result == false ==> sender != operator;
      @ ensures \result == true ==> sender == operator && pot == \old(pot) + amount;
      @ assignable pot;
      @*/
    public boolean addToPot(int amount) {
       if (sender != operator) return false;
       pot = pot + amount;
       return true;
    }

    // Proven
    // Remove money from pot
    /*@ public normal_behavior
      @ requires sender != null && operator != null && amount > 0 && State.BET_PLACED != null;
      @ ensures \result == false ==> (state == State.BET_PLACED || sender != operator);
      @ ensures \result == true ==> transfer(sender, amount) && (pot == \old(pot) - amount) && (state != State.BET_PLACED && sender == operator);
      @ assignable pot, sender.balance;
      @*/
    public boolean removeFromPot(int amount) {
        // no active bet ongoing:
        if (state == State.BET_PLACED || sender != operator) {
           return false;
        }
        transfer(sender, amount);
        pot = pot - amount;
        return true;
    }

    // Proven
    // Operator opens a bet.
    /*@ public normal_behavior
      @ requires sender != null && newHashedNumber > 0;
      @ ensures \result == false ==> state != State.IDLE || sender != operator;
      @ ensures \result == true ==> this.hashedNumber == newHashedNumber && state == State.GAME_AVAILABLE;
      @ assignable this.hashedNumber, this.state;
      @*/
    public boolean createGame(int newHashedNumber) {
        if (state != State.IDLE || sender != operator) {
            return false;
        }
        this.hashedNumber = newHashedNumber;
        this.state = State.GAME_AVAILABLE;
        return true;
    }

    // Proven
    // Player places a bet
    /*@ public normal_behavior
      @ requires sender != null && value > 0 && senderGuess != null;
      @ ensures \result == false ==> this.state != State.GAME_AVAILABLE || sender == this.operator || value > this.pot;
      @ ensures \result == true ==> state == State.BET_PLACED && player == sender && bet == value && this.guess == senderGuess;
      @ assignable this.state, this.player, this.bet, this.guess;
     */
    public boolean placeBet(int value, Coin senderGuess) {
        if (state != State.GAME_AVAILABLE || sender == operator || value > pot) {
            return false;
        }
        this.state = State.BET_PLACED;
        this.player = sender;
        this.bet = value;
        this.guess = senderGuess;
        return true;
    }

    // Proven
    // Operator resolves a bet
    /*@ public normal_behavior
      @ requires sender != null && player != null && secretNumber > 0 && bet > 0;
      @ ensures \result == false ==> state != State.BET_PLACED || sender != operator || hashedNumber != secretNumber;
      @ ensures \result == true ==> state == State.IDLE && ((secretNumber % 2 == 0 && guess == Coin.HEADS) ==> bet == 0 && pot == pot - bet && transfer(player, (int)(2*\old(bet)))) && (secretNumber % 2 != 0 && guess == Coin.TAILS ==> pot == pot + bet && bet == 0);
      @ assignable pot, bet, state, player.balance, secret;
      @*/
    public boolean decideBet(int secretNumber) {
        if (state != State.BET_PLACED || sender != operator || hashedNumber != secretNumber) {
            return false;
        }
        secret = (secretNumber % 2 == 0) ? Coin.HEADS : Coin.TAILS;
        if (secret == guess) {
            // player wins, gets back twice her bet
            pot = pot - bet;
            transfer(player, 2*bet);
            bet = 0;
        } else {
            // operator wins, bet trasnfered to pot
            pot = pot + bet;
            bet = 0;
        }
        state = State.IDLE;
        return true;
    }
}