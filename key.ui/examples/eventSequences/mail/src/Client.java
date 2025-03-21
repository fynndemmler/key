public class Client {
    private List<Mail> inbox = new ArrayList<String>();

    public void decrypt(Mail mail) {
        mail.isDecrypted = false;
    }

    public void addToInbox(Mail mail) {
        this.inbox.add(mail);
    }

    public void send(Client receiver, Mail mail) {
        decrypt(mail);
        receiver.addToInbox(mail);
    }

    public void forward(Client receiver, Mail mail) {
        decrypt(mail);
        addToInbox(mail);
        send(receiver, mail);
    }
}